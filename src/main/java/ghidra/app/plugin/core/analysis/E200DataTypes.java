/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package ghidra.app.plugin.core.analysis;

import java.util.*;

import ghidra.app.decompiler.*;
import ghidra.app.decompiler.parallel.DecompilerCallback;
import ghidra.app.decompiler.parallel.ParallelDecompiler;
import ghidra.framework.options.Options;
import ghidra.framework.store.LockException;
import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.*;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceManager;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * The data types step (part of {@link E200Analyzer}): gives global data, parameters and
 * return values of undefined type ({@code undefined1}, {@code undefined2},
 * {@code undefined4}, {@code undefined8}) the types that the decompiled functions show.
 * <p>
 * Flash images have no RAM, so RAM variables have no data: the decompiler sees one-byte
 * labels, shows the variables as {@code _DAT_...} and warns that globals overlap smaller
 * symbols. The step therefore first adds uninitialized blocks for the MPC5746R RAM that is
 * not mapped, also around dumps of part of the RAM, and creates data of the accessed size
 * where code references it. It does this at the end of analysis: with RAM mapped, Ghidra's
 * address table analysis takes flash values such as the float 2.0 (0x40000000) or pairs of
 * VLE instructions for pointers into RAM.
 * <p>
 * It then decompiles the functions with new code, their callers, which show the types of the
 * arguments, and the other functions that use the same globals, since a type is committed
 * only when all uses agree, and types from what they show, in rounds:
 * <ul>
 * <li>arrays and arrays of structures that code indexes ({@link E200Tables})</li>
 * <li>globals from their uses, and data where code uses addresses that have none
 * ({@link E200GlobalUses})</li>
 * <li>return types of functions whose callers use their result
 * ({@link E200PassedResults})</li>
 * <li>parameters, return values and globals from the values that pass between them,
 * structures and functions that pointers point to, and the width and signedness of integers
 * ({@link E200TypeFlow} with {@link E200Structures}, {@link E200FunctionPointers} and
 * {@link E200Integers})</li>
 * </ul>
 * New types change the decompiled code of the functions that use them, which then shows
 * more types: the step decompiles again those that still use undefined places or use a
 * place now typed as a pointer, three rounds at most. Optionally, the places that show no
 * type anywhere then get the unsigned integer of their size. Last, the pointers to functions
 * in flash data are typed ({@link E200FunctionPointers#apply}).
 */
final class E200DataTypes {

	private static final String OPTION_NAME = "Infer data types";
	private static final String OPTION_DESCRIPTION =
		"Give global data, parameters and return values of undefined type (undefined1,\n" +
			"undefined2, undefined4 ...) the type the decompiler infers from the functions that\n" +
			"use them or pass them on, such as float, ushort or int, when those uses agree.\n" +
			"This decompiles every function, the longest part of the analysis.";
	private static final String OPTION_NAME_RAM_BLOCKS = "Add MPC5746R RAM blocks";
	private static final String OPTION_DESCRIPTION_RAM_BLOCKS =
		"Add uninitialized blocks for the MPC5746R RAM that is not mapped, as in flash images\n" +
			"or around a dump of part of the RAM: SRAM (0x40000000), IMEM_0 (0x50000000),\n" +
			"DMEM_0 (0x50800000), IMEM_1 (0x51000000) and DMEM_1 (0x51800000), and create data\n" +
			"of the accessed size where code references them. The decompiler then shows RAM\n" +
			"variables with their size instead of _DAT_... names, and this analyzer can type them.";
	private static final boolean OPTION_DEFAULT_RAM_BLOCKS = true;
	private static final String OPTION_NAME_DEFAULTS = "Unsigned types for untyped values";
	private static final String OPTION_DESCRIPTION_DEFAULTS =
		"Give parameters, return values and globals that no code gives a type, and that are\n" +
			"not linked to a pointer, float or structure, the unsigned integer of their size\n" +
			"(byte, ushort, uint), and pointers to undefined data a pointer to it (byte * ...).\n" +
			"Functions that return nothing, whose result no caller reads, return void.";

	/** A RAM region of the MPC5746R. */
	private record RamBlock(String name, long start, long length, boolean execute,
			String description) {}

	private static final List<RamBlock> RAM_BLOCKS = List.of(
		new RamBlock("SRAM", 0x4000_0000L, 0x4_0000L, false, "System RAM"),
		new RamBlock("IMEM_0", 0x5000_0000L, 0x4000L, true, "Core 0 local instruction memory"),
		new RamBlock("DMEM_0", 0x5080_0000L, 0x8000L, false, "Core 0 local data memory"),
		new RamBlock("IMEM_1", 0x5100_0000L, 0x4000L, true, "Core 1 local instruction memory"),
		new RamBlock("DMEM_1", 0x5180_0000L, 0x8000L, false, "Core 1 local data memory"));

	private static final int DECOMPILER_TIMEOUT_SECONDS = 60;
	/** Rounds of typing, each with the functions whose code the last one changed */
	private static final int MAX_ROUNDS = 3;

	/**
	 * What a decompiled function shows: the uses of globals, the facts about the values it
	 * passes on, the globals it shows with no type, and the loads and stores at constant
	 * addresses
	 */
	record Result(Function function, List<E200GlobalUses.Use> uses, E200TypeFlow.Facts facts,
			List<Address> untyped, List<E200Tables.Access> indexed) {}

	/** What the step did, for the log */
	private static final class Counts {
		int tables;
		int data;
		int globals;
		int passed;
		int fromValues;
		int byDefault;
		int voids;
	}

	private boolean enabled = true;
	private boolean addRamBlocksOption = OPTION_DEFAULT_RAM_BLOCKS;
	private boolean defaultsOption = true;

	void registerOptions(Options options) {
		options.registerOption(OPTION_NAME, enabled, null, OPTION_DESCRIPTION);
		options.registerOption(OPTION_NAME_RAM_BLOCKS, addRamBlocksOption, null,
			OPTION_DESCRIPTION_RAM_BLOCKS);
		options.registerOption(OPTION_NAME_DEFAULTS, defaultsOption, null,
			OPTION_DESCRIPTION_DEFAULTS);
	}

	void optionsChanged(Options options) {
		enabled = options.getBoolean(OPTION_NAME, enabled);
		addRamBlocksOption = options.getBoolean(OPTION_NAME_RAM_BLOCKS, addRamBlocksOption);
		defaultsOption = options.getBoolean(OPTION_NAME_DEFAULTS, defaultsOption);
	}

	/**
	 * Adds the RAM blocks that are not there yet, at the end of every analysis (see the class
	 * comment), creates data where code accesses RAM that has none, and types the globals,
	 * parameters and return values that the functions use.
	 */
	boolean apply(Program program, Set<Function> analyzed, TaskMonitor monitor)
			throws CancelledException {
		if (!enabled) {
			return true;
		}
		if (addRamBlocksOption) {
			addRamBlocks(program);
			createAccessedData(program, unmappedRam(program), monitor);
		}
		if (analyzed.isEmpty()) {
			return true;
		}
		try {
			monitor.setMessage(E200Analyzer.NAME + " - decompiling");
			// their callers too, which show the types of the arguments
			Set<Function> functions = new HashSet<>(analyzed);
			for (Function f : analyzed) {
				functions.addAll(callers(f, monitor));
			}
			Map<Function, Result> results = new HashMap<>();
			decompile(program, functions, results, monitor);

			// A type is only committed when all uses agree, so also look at the uses in
			// functions outside the analyzed set.
			Set<Address> globals = new HashSet<>();
			for (Result r : results.values()) {
				for (E200GlobalUses.Use use : r.uses()) {
					globals.add(use.address());
				}
			}
			Set<Function> others = using(program, globals);
			others.removeAll(results.keySet());
			decompile(program, others, results, monitor);

			// parameters and return values are typed only when all callers are decompiled
			Set<Function> complete = new HashSet<>();
			for (Function f : results.keySet()) {
				if (results.keySet().containsAll(callers(f, monitor))) {
					complete.add(f);
				}
			}

			Counts counts = new Counts();
			E200PassedResults passed = new E200PassedResults(program);
			E200Tables tables = new E200Tables(program);
			for (int round = 1; round <= MAX_ROUNDS; round++) {
				monitor.setMessage(E200Analyzer.NAME + " - applying");
				Set<Address> changedGlobals = new HashSet<>();
				Set<Function> changedFunctions = new HashSet<>();
				if (typeRound(program, results.values(), functions, complete, changedGlobals,
					changedFunctions, false, passed, tables, counts, monitor) == 0) {
					break;
				}
				Set<Function> affected = affected(program, results, tables, changedGlobals,
					changedFunctions, monitor);
				monitor.setMessage(E200Analyzer.NAME + " - decompiling again");
				decompile(program, affected, results, monitor);
			}
			if (defaultsOption) {
				typeRound(program, results.values(), functions, complete, new HashSet<>(),
					new HashSet<>(), true, passed, tables, counts, monitor);
				// with default types, code shows more of what the pointers in tables that are
				// still untyped point to, as in (uint *)tbl[i].f4 where the value goes to a
				// global now typed uint
				Set<Function> open = new HashSet<>();
				for (Result r : results.values()) {
					if (usesOpenField(tables, r)) {
						open.add(r.function());
					}
				}
				if (!open.isEmpty()) {
					monitor.setMessage(E200Analyzer.NAME + " - decompiling again");
					decompile(program, open, results, monitor);
					typeRound(program, results.values(), functions, complete, new HashSet<>(),
						new HashSet<>(), false, passed, tables, counts, monitor);
				}
			}
			int functionPointers = E200FunctionPointers.apply(program, monitor);
			log(counts, functionPointers);
		}
		catch (CancelledException | InterruptedException e) {
			throw new CancelledException();
		}
		catch (Exception e) {
			Msg.error(E200Analyzer.class, "Data type inference failed", e);
		}
		return true;
	}

	/**
	 * One round of typing with what the decompiled functions show: tables, globals from
	 * their uses, results callers use, and places from the values passed to them; optionally
	 * the default types.
	 *
	 * @param functions the analyzed functions and their callers, whose globals are typed
	 * @param complete the functions whose callers were all decompiled
	 * @param changedGlobals gets the globals typed or created
	 * @param changedFunctions gets the functions whose parameters or return values are typed
	 * @param defaults whether to give the places no code gives a type a default type
	 * @return the number of changes
	 */
	private static int typeRound(Program program, Collection<Result> results,
			Set<Function> functions, Set<Function> complete, Set<Address> changedGlobals,
			Set<Function> changedFunctions, boolean defaults, E200PassedResults passed,
			E200Tables tables, Counts counts, TaskMonitor monitor) throws CancelledException {
		E200GlobalUses.Round uses = new E200GlobalUses.Round(program, results, functions);
		List<E200Tables.Access> indexed = new ArrayList<>();
		for (Result result : results) {
			indexed.addAll(result.indexed());
		}
		counts.tables += tables.update(indexed, defaults, changedGlobals, monitor);
		counts.data += uses.applyStructures(changedGlobals);
		counts.data += uses.createData(changedGlobals);
		counts.globals += uses.typeFromUses(changedGlobals, monitor);

		// before the functions that return nothing are given void
		List<Function> passing = passed.apply(monitor);
		counts.passed += passing.size();
		changedFunctions.addAll(passing);
		E200TypeFlow.Typed flow = E200TypeFlow.apply(program, uses.facts, uses.types,
			uses.typable, complete, defaults, monitor);
		// and after, for the functions whose results the flow typed: a wrapper given void
		// then returns their type
		passing = passed.apply(monitor);
		counts.passed += passing.size();
		changedFunctions.addAll(passing);
		counts.fromValues += flow.fromValues().size();
		counts.byDefault += flow.byDefault().size();
		counts.voids += flow.voids().size();
		for (Function f : passing) {
			if (flow.voids().contains(new E200TypeFlow.Return(f.getEntryPoint()))) {
				counts.voids--;
			}
		}
		for (E200TypeFlow.Slot slot : flow.fromValues()) {
			if (slot instanceof E200TypeFlow.Global g) {
				changedGlobals.add(g.address());
			}
			else if (slot.function(program) != null) {
				changedFunctions.add(slot.function(program));
			}
		}
		return changedGlobals.size() + changedFunctions.size();
	}

	/**
	 * The decompiled functions whose code the new types change, and that can show more: those
	 * that use a changed global, table field or function and still use an undefined place or
	 * table field, or a place now typed as a pointer, which shows the places it points to
	 */
	private static Set<Function> affected(Program program, Map<Function, Result> results,
			E200Tables tables, Set<Address> changedGlobals, Set<Function> changedFunctions,
			TaskMonitor monitor) {
		Set<Function> affected = using(program, changedGlobals);
		Set<Function> pointing = using(program, pointers(program, changedGlobals));
		for (Result r : results.values()) {
			for (E200GlobalUses.Use u : r.uses()) {
				if (changedGlobals.contains(u.address())) {
					affected.add(r.function());
				}
			}
			for (E200Tables.Access a : r.indexed()) {
				if (changedGlobals.contains(a.address())) {
					affected.add(r.function());
				}
			}
		}
		for (Function f : changedFunctions) {
			affected.add(f);
			affected.addAll(callers(f, monitor));
			if (hasPointer(f)) {
				pointing.add(f);
				pointing.addAll(callers(f, monitor));
			}
		}
		affected.retainAll(results.keySet());
		affected.removeIf(f -> !pointing.contains(f) &&
			!usesOpenPlace(program, results.get(f)) && !usesOpenField(tables, results.get(f)));
		return affected;
	}

	private static void log(Counts counts, int functionPointers) {
		if (functionPointers > 0) {
			Msg.info(E200Analyzer.class, "Typed " + functionPointers +
				" pointers, array elements and structure fields in flash that point to functions");
		}
		if (counts.tables > 0) {
			Msg.info(E200Analyzer.class, "Created " + counts.tables +
				" arrays and arrays of structures that code indexes");
		}
		if (counts.data > 0) {
			Msg.info(E200Analyzer.class, "Created data at " + counts.data +
				" arrays that code indexes and addresses it uses as pointers");
		}
		if (counts.globals > 0) {
			Msg.info(E200Analyzer.class,
				"Typed " + counts.globals + " global variables from their uses");
		}
		if (counts.fromValues > 0) {
			Msg.info(E200Analyzer.class, "Typed " + counts.fromValues +
				" parameters, return values and globals from the values passed to them");
		}
		if (counts.byDefault > 0) {
			Msg.info(E200Analyzer.class, "Gave " + counts.byDefault +
				" untyped parameters, return values and globals an unsigned type");
		}
		if (counts.voids > 0) {
			Msg.info(E200Analyzer.class, "Gave " + counts.voids +
				" functions that return nothing the return type void");
		}
		if (counts.passed > 0) {
			Msg.info(E200Analyzer.class, "Gave " + counts.passed +
				" functions whose callers use their result a return type");
		}
	}

	/**
	 * Whether a decompiled function uses a place that may still get a type: global data of
	 * undefined type or an address without data, or a parameter or return value of undefined
	 * type
	 */
	private static boolean usesOpenPlace(Program program, Result result) {
		Listing listing = program.getListing();
		for (E200GlobalUses.Use use : result.uses()) {
			Data data = listing.getDefinedDataAt(use.address());
			if (data == null ? use.access() != E200GlobalUses.Access.VALUE
					: Undefined.isUndefined(data.getDataType())) {
				return true;
			}
		}
		for (Address addr : result.untyped()) {
			Data data = listing.getDefinedDataAt(addr);
			if (data == null || Undefined.isUndefined(data.getDataType())) {
				return true;
			}
		}
		for (Map.Entry<E200TypeFlow.Slot, DataType> t : result.facts().types) {
			if (E200TypeFlow.open(program, t.getKey())) {
				return true;
			}
		}
		return false;
	}

	/** Whether a function accesses a table field that is untyped or points to undefined */
	private static boolean usesOpenField(E200Tables tables, Result result) {
		for (E200Tables.Access a : result.indexed()) {
			if (tables.openField(a.address())) {
				return true;
			}
		}
		return false;
	}

	/** The globals typed as pointers */
	private static Set<Address> pointers(Program program, Set<Address> globals) {
		Set<Address> pointers = new HashSet<>();
		for (Address addr : globals) {
			Data data = program.getListing().getDefinedDataAt(addr);
			if (data != null && data.getDataType() instanceof Pointer) {
				pointers.add(addr);
			}
		}
		return pointers;
	}

	/** Whether a function takes or returns a pointer */
	private static boolean hasPointer(Function f) {
		if (f.getReturnType() instanceof Pointer) {
			return true;
		}
		for (Parameter p : f.getParameters()) {
			if (p.getDataType() instanceof Pointer) {
				return true;
			}
		}
		return false;
	}

	/** The functions that reference the addresses */
	private static Set<Function> using(Program program, Set<Address> addresses) {
		Set<Function> using = new HashSet<>();
		FunctionManager manager = program.getFunctionManager();
		for (Address addr : addresses) {
			for (Reference ref : program.getReferenceManager().getReferencesTo(addr)) {
				Function f = manager.getFunctionContaining(ref.getFromAddress());
				if (f != null && !f.isThunk()) {
					using.add(f);
				}
			}
		}
		return using;
	}

	/** The functions that call a function, directly or through a thunk */
	private static Set<Function> callers(Function f, TaskMonitor monitor) {
		Set<Function> callers = new HashSet<>(f.getCallingFunctions(monitor));
		Address[] thunks = f.getFunctionThunkAddresses(true);
		if (thunks != null) {
			FunctionManager manager = f.getProgram().getFunctionManager();
			for (Address a : thunks) {
				Function thunk = manager.getFunctionAt(a);
				if (thunk != null) {
					callers.addAll(thunk.getCallingFunctions(monitor));
				}
			}
		}
		callers.removeIf(c -> c.isThunk() || c.isExternal());
		return callers;
	}

	/**
	 * Decompiles the functions and keeps, for each, what it shows: the uses of globals, the
	 * facts about the values it passes on, and the loads and stores at constant addresses.
	 */
	private static void decompile(Program program, Collection<Function> functions,
			Map<Function, Result> results, TaskMonitor monitor) throws Exception {
		if (functions.isEmpty()) {
			return;
		}
		DecompilerCallback<Result> callback =
			new DecompilerCallback<>(program, decompiler -> {
				DecompileOptions options = new DecompileOptions();
				options.grabFromProgram(program);
				decompiler.setOptions(options);
				decompiler.toggleCCode(false);
				decompiler.toggleSyntaxTree(true);
				decompiler.setSimplificationStyle("decompile");
			}) {
				@Override
				public Result process(DecompileResults results, TaskMonitor m) {
					HighFunction high = results.getHighFunction();
					return high == null ? null
							: new Result(results.getFunction(), E200GlobalUses.collect(high),
								E200TypeFlow.collect(high), E200GlobalUses.untyped(high),
								E200Tables.collect(high));
				}
			};
		callback.setTimeout(DECOMPILER_TIMEOUT_SECONDS);
		try {
			for (Result result : ParallelDecompiler.decompileFunctions(callback, functions,
				monitor)) {
				if (result != null) {
					results.put(result.function(), result);
				}
			}
		}
		finally {
			callback.dispose();
		}
	}

	// ---- RAM ----------------------------------------------------------------------------------

	/**
	 * Adds blocks for the parts of the MPC5746R RAM that have nothing mapped, such as the
	 * space around a dump of part of the RAM. A part is named after its RAM with its start
	 * address ({@code SRAM_40000000}) unless it is the whole RAM.
	 */
	private static void addRamBlocks(Program program) {
		List<String> names = new ArrayList<>();
		Memory memory = program.getMemory();
		AddressSpace space = program.getAddressFactory().getDefaultAddressSpace();
		for (RamBlock ram : RAM_BLOCKS) {
			Address start = space.getAddress(ram.start());
			Address end = space.getAddress(ram.start() + ram.length() - 1);
			for (AddressRange range : new AddressSet(start, end).subtract(memory)) {
				String name = range.getLength() == ram.length() ? ram.name()
						: ram.name() + "_" + range.getMinAddress();
				try {
					MemoryBlock block = memory.createUninitializedBlock(name,
						range.getMinAddress(), range.getLength(), false);
					block.setPermissions(true, true, ram.execute());
					block.setComment(ram.description() + ", added by " + E200Analyzer.NAME);
					names.add(name);
				}
				catch (LockException | MemoryConflictException | AddressOverflowException e) {
					Msg.info(E200Analyzer.class,
						"Could not add " + name + ": " + e.getMessage());
				}
			}
		}
		if (!names.isEmpty()) {
			Msg.info(E200Analyzer.class, "Added RAM blocks " + String.join(", ", names));
		}
	}

	/** The MPC5746R RAM in uninitialized blocks, as the analyzer adds them */
	private static AddressSetView unmappedRam(Program program) {
		AddressSet ram = new AddressSet();
		AddressSpace space = program.getAddressFactory().getDefaultAddressSpace();
		for (RamBlock block : RAM_BLOCKS) {
			ram.add(space.getAddress(block.start()),
				space.getAddress(block.start() + block.length() - 1));
		}
		AddressSet unmapped = new AddressSet();
		for (MemoryBlock block : program.getMemory().getBlocks()) {
			if (!block.isInitialized()) {
				unmapped.add(block.getStart(), block.getEnd());
			}
		}
		return ram.intersect(unmapped);
	}

	/**
	 * Creates undefined data of the accessed size at each address in the given ranges that
	 * instructions reference, as the reference analysis does for memory that exists when it
	 * runs.
	 */
	private static void createAccessedData(Program program, AddressSetView ranges,
			TaskMonitor monitor) throws CancelledException {
		Listing listing = program.getListing();
		ReferenceManager references = program.getReferenceManager();
		// forward only: backward iteration over an address set starts at its minimum
		AddressIterator it = references.getReferenceDestinationIterator(ranges, true);
		while (it.hasNext()) {
			monitor.checkCancelled();
			Address addr = it.next();
			List<Integer> sizes = new ArrayList<>();
			for (Reference ref : references.getReferencesTo(addr)) {
				int size = E200Code.accessSize(listing.getInstructionAt(ref.getFromAddress()));
				if (size > 0) {
					sizes.add(size);
				}
			}
			int size = E200Types.mostFrequent(sizes);
			if (size == 0) {
				continue;
			}
			try {
				Address end = addr.addNoWrap(size - 1);
				if (ranges.contains(addr, end) && listing.isUndefined(addr, end)) {
					listing.createData(addr, Undefined.getUndefinedDataType(size));
				}
			}
			catch (AddressOverflowException | CodeUnitInsertionException e) {
				// no room for the access at this address
			}
		}
	}
}
