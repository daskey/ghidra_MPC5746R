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
import ghidra.program.model.data.Enum;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceManager;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Gives global data of undefined type ({@code undefined1}, {@code undefined2},
 * {@code undefined4}, {@code undefined8}) the type the decompiler infers from the functions
 * that use it (part of {@link E200Analyzer}).
 * <p>
 * The reference analysis creates such data wherever code loads or stores a global, knowing
 * only the access size. The decompiler usually knows more: a value used by {@code efs*}
 * instructions is a {@code float}, one that is sign extended is signed, one that is
 * dereferenced is a pointer. A type is committed only when all uses agree, except that a
 * {@code float} use wins over integer uses of the same size (values that are only copied
 * look like integers) and integer uses that differ only in signedness go to a clear
 * majority. Single bytes get {@code byte} or {@code sbyte} rather than a character type.
 * <p>
 * Flash images have no RAM, so RAM variables have no data: the decompiler sees one-byte
 * labels, shows the variables as {@code _DAT_...} and warns that globals overlap smaller
 * symbols. The analyzer therefore first adds uninitialized blocks for the MPC5746R RAM
 * that is not mapped, also around dumps of part of the RAM, and creates data of the
 * accessed size where code references it. It
 * does this at the end of analysis: with RAM mapped, Ghidra's address table analysis takes
 * flash values such as the float 2.0 (0x40000000) or pairs of VLE instructions for
 * pointers into RAM.
 * <p>
 * Arrays that code indexes, loading or storing at their address plus an index, have no
 * reference to their start, and tables in flash that code passes by address have no data.
 * They get data of the element size or of the size of the pointer's target, typed from the
 * uses, so that the decompiler shows {@code (&BYTE_4000e46e)[i]} instead of
 * {@code *(undefined1 *)(i + 0x4000e46e)} and {@code &SHORT_09294ba0} instead of
 * {@code (short *)&DAT_09294ba0}.
 * <p>
 * Parameters and return values that the functions only copy, and globals they are copied
 * to and from, get the types the values have where they come from or go to (see
 * {@link E200TypeFlow}). Optionally, those that show no type anywhere get the unsigned
 * integer of their size.
 * <p>
 * New types change the decompiled code of the functions that use them, which then shows
 * more types: the analyzer decompiles again those that still use undefined places or use a
 * place now typed as a pointer, three rounds at most.
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

	private boolean enabled = true;
	private boolean addRamBlocksOption = OPTION_DEFAULT_RAM_BLOCKS;
	private boolean defaultsOption = true;

	/** How code uses a global */
	private enum Access {
		/** the value of the global symbol */
		VALUE,
		/** a load or store at its address plus an index, of an array */
		INDEXED,
		/** its address, as a pointer to the type */
		ADDRESS
	}

	/**
	 * A use of a global seen by the decompiler: its address, the inferred type and the size
	 * of the access.
	 */
	private record Use(Address address, DataType type, int size, Access access) {}

	/**
	 * What a decompiled function shows about globals and the values it passes on, and the
	 * globals it shows with no type
	 */
	private record Result(Function function, List<Use> uses, E200TypeFlow.Facts facts,
			List<Address> untyped) {}

	/** Rounds of typing, each with the functions whose code the last one changed */
	private static final int MAX_ROUNDS = 3;

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
	 * Adds the RAM blocks, at the end of analysis (see the class comment), and types the
	 * globals, parameters and return values that the functions use.
	 */
	boolean apply(Program program, Set<Function> analyzed, TaskMonitor monitor)
			throws CancelledException {
		if (!enabled) {
			return true;
		}
		if (addRamBlocksOption) {
			AddressSetView ram = addRamBlocks(program);
			if (!ram.isEmpty()) {
				createAccessedData(program, ram, monitor);
			}
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
				for (Use use : r.uses()) {
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

			// globals from their uses, arrays, places from values, places by default, voids
			int[] typed = new int[5];
			for (int round = 1; round <= MAX_ROUNDS; round++) {
				monitor.setMessage(E200Analyzer.NAME + " - applying");
				Set<Address> changedGlobals = new HashSet<>();
				Set<Function> changedFunctions = new HashSet<>();
				if (typeRound(program, results.values(), functions, complete, changedGlobals,
					changedFunctions, false, typed, monitor) == 0) {
					break;
				}
				// the functions whose code the new types change
				Set<Function> affected = using(program, changedGlobals);
				Set<Function> pointing = using(program, pointers(program, changedGlobals));
				for (Function f : changedFunctions) {
					affected.add(f);
					affected.addAll(callers(f, monitor));
					if (hasPointer(f)) {
						pointing.add(f);
						pointing.addAll(callers(f, monitor));
					}
				}
				affected.retainAll(results.keySet());
				// only those that still use an undefined place, or a place now typed as a
				// pointer, which shows the places it points to, can show more
				affected.removeIf(
					f -> !pointing.contains(f) && !usesOpenPlace(program, results.get(f)));
				monitor.setMessage(E200Analyzer.NAME + " - decompiling again");
				decompile(program, affected, results, monitor);
			}
			if (defaultsOption) {
				typeRound(program, results.values(), functions, complete, new HashSet<>(),
					new HashSet<>(), true, typed, monitor);
			}
			if (typed[1] > 0) {
				Msg.info(E200Analyzer.class, "Created data at " + typed[1] +
					" arrays that code indexes and addresses it uses as pointers");
			}
			if (typed[0] > 0) {
				Msg.info(E200Analyzer.class,
					"Typed " + typed[0] + " global variables from their uses");
			}
			if (typed[2] > 0) {
				Msg.info(E200Analyzer.class, "Typed " + typed[2] +
					" parameters, return values and globals from the values passed to them");
			}
			if (typed[3] > 0) {
				Msg.info(E200Analyzer.class, "Gave " + typed[3] +
					" untyped parameters, return values and globals an unsigned type");
			}
			if (typed[4] > 0) {
				Msg.info(E200Analyzer.class, "Gave " + typed[4] +
					" functions that return nothing the return type void");
			}
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
	 * Types globals from their uses, creates data at arrays and addresses used as pointers
	 * and types places from the values passed to them, with what the decompiled functions
	 * show, and optionally gives the untyped places default types. Only the globals that
	 * the analyzed functions and their callers use are typed: the other decompiled functions
	 * are there for the other uses of these globals.
	 *
	 * @param changedGlobals gets the globals typed or created
	 * @param changedFunctions gets the functions whose parameters or return values are typed
	 * @param defaults whether to give the places no code gives a type a default type
	 * @param typed counts of globals typed, arrays created, places typed, places given a
	 * default type and functions given a void return type, added to
	 * @return the number of changes
	 */
	private static int typeRound(Program program, Collection<Result> results,
			Set<Function> functions, Set<Function> complete, Set<Address> changedGlobals,
			Set<Function> changedFunctions, boolean defaults, int[] typed, TaskMonitor monitor)
			throws CancelledException {
		Listing listing = program.getListing();
		Set<Address> typable = new HashSet<>();
		for (Result result : results) {
			if (functions.contains(result.function())) {
				for (Use use : result.uses()) {
					typable.add(use.address());
				}
				typable.addAll(result.facts().globals());
			}
		}
		Map<Address, List<DataType>> uses = new HashMap<>();
		Map<Address, List<Use>> undefined = new TreeMap<>(); // uses where there is no data
		List<E200TypeFlow.Facts> facts = new ArrayList<>();
		// the types of the elements of arrays, for the default types
		E200TypeFlow.Facts elements = new E200TypeFlow.Facts();
		facts.add(elements);
		for (Result result : results) {
			facts.add(result.facts());
			for (Use use : result.uses()) {
				if (!typable.contains(use.address())) {
					continue;
				}
				Data data = listing.getDefinedDataAt(use.address());
				if (data == null && use.access() != Access.VALUE) {
					undefined.computeIfAbsent(use.address(), a -> new ArrayList<>()).add(use);
				}
				else if (data != null && Undefined.isUndefined(data.getDataType()) &&
					use.type() != null && use.type().getLength() == data.getLength()) {
					if (!Undefined.isUndefined(use.type())) {
						uses.computeIfAbsent(use.address(), a -> new ArrayList<>())
								.add(use.type());
					}
					if (use.access() == Access.INDEXED) {
						elements.type(new E200TypeFlow.Global(use.address()), use.type());
					}
				}
			}
		}
		List<Address> created = createData(program, undefined, uses);
		changedGlobals.addAll(created);
		typed[1] += created.size();

		boolean signedChar = program.getDataTypeManager().getDataOrganization().isSignedChar();
		for (Map.Entry<Address, List<DataType>> e : uses.entrySet()) {
			monitor.checkCancelled();
			DataType type = chooseType(e.getValue(), signedChar, true);
			if (type != null && applyType(program, e.getKey(), type)) {
				changedGlobals.add(e.getKey());
				typed[0]++;
			}
		}
		FunctionManager manager = program.getFunctionManager();
		E200TypeFlow.Typed flow =
			E200TypeFlow.apply(program, facts, uses, typable, complete, defaults, monitor);
		typed[2] += flow.fromValues().size();
		typed[3] += flow.byDefault().size();
		typed[4] += flow.voids().size();
		for (E200TypeFlow.Slot slot : flow.fromValues()) {
			Address function = null;
			if (slot instanceof E200TypeFlow.Global g) {
				changedGlobals.add(g.address());
			}
			else if (slot instanceof E200TypeFlow.Param p) {
				function = p.function();
			}
			else if (slot instanceof E200TypeFlow.Return r) {
				function = r.function();
			}
			if (function != null && manager.getFunctionAt(function) != null) {
				changedFunctions.add(manager.getFunctionAt(function));
			}
		}
		return changedGlobals.size() + changedFunctions.size();
	}

	/**
	 * Whether a decompiled function uses a place that may still get a type: global data of
	 * undefined type or an address without data, or a parameter or return value of undefined
	 * type
	 */
	private static boolean usesOpenPlace(Program program, Result result) {
		Listing listing = program.getListing();
		for (Use use : result.uses()) {
			Data data = listing.getDefinedDataAt(use.address());
			if (data == null ? use.access() != Access.VALUE
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
	 * Adds blocks for the parts of the MPC5746R RAM that have nothing mapped, such as the
	 * space around a dump of part of the RAM. A part is named after its RAM with its start
	 * address ({@code SRAM_40000000}) unless it is the whole RAM.
	 *
	 * @return the address ranges of the added blocks
	 */
	private static AddressSetView addRamBlocks(Program program) {
		AddressSet added = new AddressSet();
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
					added.add(range);
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
		return added;
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
			// the most frequent access size, the larger one on a tie
			Map<Integer, Integer> counts = new HashMap<>();
			for (Reference ref : references.getReferencesTo(addr)) {
				Instruction instr = listing.getInstructionAt(ref.getFromAddress());
				int size = instr == null ? 0 : accessSize(instr);
				if (size > 0) {
					counts.merge(size, 1, Integer::sum);
				}
			}
			int size = 0, count = 0;
			for (Map.Entry<Integer, Integer> e : counts.entrySet()) {
				if (e.getValue() > count || (e.getValue() == count && e.getKey() > size)) {
					size = e.getKey();
					count = e.getValue();
				}
			}
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

	/** Returns the size of the loads or stores of an instruction, or 0 if they differ. */
	private static int accessSize(Instruction instr) {
		int size = 0;
		for (PcodeOp op : instr.getPcode()) {
			int opSize = switch (op.getOpcode()) {
				case PcodeOp.LOAD -> op.getOutput().getSize();
				case PcodeOp.STORE -> op.getInput(2).getSize();
				default -> 0;
			};
			if (opSize != 0) {
				if (size != 0 && size != opSize) {
					return 0;
				}
				size = opSize;
			}
		}
		return size;
	}

	/**
	 * Decompiles the functions and keeps, for each, the uses of globals and the facts about
	 * the values it passes on.
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
							: new Result(results.getFunction(), globalUses(high),
								E200TypeFlow.collect(high), untypedGlobals(high));
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

	/**
	 * Creates data where code uses an address that has none: the start of arrays that code
	 * accesses at their address plus an index, and addresses that code uses as pointers to a
	 * type, such as a table in flash passed as a {@code short *}. The data is of the most
	 * frequent size of the accesses, and their types are added to the uses. The decompiler
	 * then shows {@code (&BYTE_4000e46e)[i]} instead of {@code *(byte *)(i + 0x4000e46e)},
	 * and {@code &SHORT_09294ba0} instead of {@code (short *)&DAT_09294ba0}.
	 *
	 * @return the addresses given data
	 */
	private static List<Address> createData(Program program, Map<Address, List<Use>> undefined,
			Map<Address, List<DataType>> uses) {
		Listing listing = program.getListing();
		Memory memory = program.getMemory();
		FunctionManager functions = program.getFunctionManager();
		List<Address> created = new ArrayList<>();
		for (Map.Entry<Address, List<Use>> e : undefined.entrySet()) {
			Address base = e.getKey();
			MemoryBlock block = memory.getBlock(base);
			// RAM or flash, not a peripheral, and not in the code of a function
			if (block == null || block.isVolatile() ||
				functions.getFunctionContaining(base) != null) {
				continue;
			}
			Map<Integer, Integer> counts = new HashMap<>();
			for (Use use : e.getValue()) {
				counts.merge(use.size(), 1, Integer::sum);
			}
			int size = 0, count = 0;
			for (Map.Entry<Integer, Integer> c : counts.entrySet()) {
				if (c.getValue() > count || (c.getValue() == count && c.getKey() > size)) {
					size = c.getKey();
					count = c.getValue();
				}
			}
			if (size != 1 && size != 2 && size != 4 && size != 8 ||
				base.getOffset() % size != 0) {
				continue;
			}
			try {
				Address end = base.addNoWrap(size - 1);
				if (!block.contains(end) || !listing.isUndefined(base, end)) {
					continue;
				}
				listing.createData(base, Undefined.getUndefinedDataType(size));
			}
			catch (AddressOverflowException | CodeUnitInsertionException ex) {
				continue;
			}
			created.add(base);
			for (Use use : e.getValue()) {
				if (use.size() == size && use.type() != null &&
					!Undefined.isUndefined(use.type()) && use.type().getLength() == size) {
					uses.computeIfAbsent(base, a -> new ArrayList<>()).add(use.type());
				}
			}
		}
		return created;
	}

	/** The globals a decompiled function reads or writes with an undefined type */
	private static List<Address> untypedGlobals(HighFunction high) {
		List<Address> untyped = new ArrayList<>();
		Iterator<HighSymbol> it = high.getGlobalSymbolMap().getSymbols();
		while (it.hasNext()) {
			HighSymbol symbol = it.next();
			HighVariable variable = symbol.getHighVariable();
			if (variable != null && symbol.getStorage() != null &&
				symbol.getStorage().isMemoryStorage() &&
				Undefined.isUndefined(variable.getDataType())) {
				untyped.add(symbol.getStorage().getMinAddress());
			}
		}
		return untyped;
	}

	private static List<Use> globalUses(HighFunction high) {
		List<Use> uses = new ArrayList<>();
		Iterator<HighSymbol> it = high.getGlobalSymbolMap().getSymbols();
		while (it.hasNext()) {
			HighSymbol symbol = it.next();
			HighVariable variable = symbol.getHighVariable();
			if (variable == null || symbol.getStorage() == null ||
				!symbol.getStorage().isMemoryStorage()) {
				continue;
			}
			DataType type = variable.getDataType();
			if (type != null && !Undefined.isUndefined(type) &&
				type.getLength() == symbol.getSize()) {
				uses.add(new Use(symbol.getStorage().getMinAddress(), type, type.getLength(),
					Access.VALUE));
			}
		}
		AddressSpace space =
			high.getFunction().getProgram().getAddressFactory().getDefaultAddressSpace();
		long max = space.getMaxAddress().getOffset();
		Iterator<PcodeOpAST> ops = high.getPcodeOps();
		while (ops.hasNext()) {
			PcodeOpAST op = ops.next();
			int opcode = op.getOpcode();
			if (opcode == PcodeOp.PTRSUB && op.getInput(0).isConstant() &&
				op.getInput(0).getOffset() == 0 && op.getInput(1).isConstant()) {
				// the address of a global, used as a pointer: to itself or to the cast type
				long target = op.getInput(1).getOffset();
				if (target > 0 && target <= max) {
					for (DataType type : pointedTo(op.getOutput())) {
						uses.add(new Use(space.getAddress(target), type, type.getLength(),
							Access.ADDRESS));
					}
				}
				continue;
			}
			if (opcode != PcodeOp.LOAD && opcode != PcodeOp.STORE) {
				continue;
			}
			Varnode value = opcode == PcodeOp.LOAD ? op.getOutput() : op.getInput(2);
			long base = constantBase(op.getInput(1), 0);
			if (value == null || base <= 0 || base > max) {
				continue;
			}
			HighVariable variable = value.getHigh();
			uses.add(new Use(space.getAddress(base),
				variable == null ? null : variable.getDataType(), value.getSize(),
				Access.INDEXED));
		}
		return uses;
	}

	/**
	 * The types a pointer points to, as its own type and the types it is cast to, where they
	 * are numbers or pointers of 1, 2, 4 or 8 bytes
	 */
	private static List<DataType> pointedTo(Varnode pointer) {
		List<DataType> types = new ArrayList<>();
		List<Varnode> views = new ArrayList<>();
		views.add(pointer);
		Iterator<PcodeOp> uses = pointer.getDescendants();
		while (uses.hasNext()) {
			PcodeOp use = uses.next();
			if (use.getOpcode() == PcodeOp.CAST && use.getOutput() != null) {
				views.add(use.getOutput());
			}
		}
		for (Varnode v : views) {
			HighVariable high = v.getHigh();
			if (high != null && high.getDataType() instanceof Pointer p &&
				E200TypeFlow.informative(p)) {
				DataType target = p.getDataType();
				int length = target.getLength();
				if (kind(target) != Kind.OTHER &&
					(length == 1 || length == 2 || length == 4 || length == 8)) {
					types.add(target);
				}
			}
		}
		return types;
	}

	/**
	 * The constant in an address computed as a constant plus an index, as in
	 * {@code i * 2 + 0x4000b020} or {@code (&DAT_4000b020)[i]}, or -1.
	 */
	private static long constantBase(Varnode address, int depth) {
		PcodeOp def = address == null || depth > 3 ? null : address.getDef();
		if (def == null) {
			return -1;
		}
		switch (def.getOpcode()) {
			case PcodeOp.INT_ADD: {
				Varnode a = def.getInput(0);
				Varnode b = def.getInput(1);
				if (a.isConstant() != b.isConstant()) {
					return (a.isConstant() ? a : b).getOffset();
				}
				long base = constantBase(a, depth + 1);
				return base >= 0 ? base : constantBase(b, depth + 1);
			}
			case PcodeOp.PTRSUB: // the address of a global, &DAT_...
				return def.getInput(0).isConstant() && def.getInput(0).getOffset() == 0 &&
					def.getInput(1).isConstant() ? def.getInput(1).getOffset() : -1;
			case PcodeOp.PTRADD: // an element of it, (&DAT_...)[i]
			case PcodeOp.CAST:
			case PcodeOp.COPY:
				return constantBase(def.getInput(0), depth + 1);
			default:
				return -1;
		}
	}

	private enum Kind {
		FLOAT, INTEGER, POINTER, OTHER
	}

	private static Kind kind(DataType type) {
		DataType base = type instanceof TypeDef t ? t.getBaseDataType() : type;
		if (base instanceof AbstractFloatDataType) {
			return Kind.FLOAT;
		}
		if (base instanceof AbstractIntegerDataType || base instanceof Enum) {
			return Kind.INTEGER;
		}
		if (base instanceof Pointer) {
			return Kind.POINTER;
		}
		return Kind.OTHER;
	}

	/**
	 * Chooses the type for a global from the types its uses were given, or returns null
	 * when they disagree.
	 *
	 * @param types the types of the uses
	 * @param signedChar whether plain {@code char} is signed in the program
	 * @param floatWins whether a {@code float} wins over integers of its size, as for the uses
	 * of one global, where values that are only copied look like integers
	 * @return the type or null
	 */
	static DataType chooseType(List<DataType> types, boolean signedChar, boolean floatWins) {
		Map<String, DataType> distinct = new LinkedHashMap<>();
		Map<String, Integer> counts = new HashMap<>();
		for (DataType type : types) {
			if (kind(type) == Kind.OTHER) {
				return null;
			}
			String key = type.getPathName() + "/" + type.getLength();
			distinct.putIfAbsent(key, type);
			counts.merge(key, 1, Integer::sum);
		}
		DataType chosen = null;
		if (distinct.size() == 1) {
			chosen = distinct.values().iterator().next();
		}
		else if (!distinct.isEmpty()) {
			int length = -1;
			List<DataType> floats = new ArrayList<>();
			for (DataType type : distinct.values()) {
				if (length >= 0 && type.getLength() != length) {
					return null;
				}
				length = type.getLength();
				switch (kind(type)) {
					case FLOAT -> floats.add(type);
					case INTEGER -> {
						// copies and bit tests of a value look like integer uses
					}
					default -> {
						return null;
					}
				}
			}
			if (floats.size() == 1 && floatWins) {
				chosen = floats.get(0);
			}
			else if (floats.isEmpty()) {
				// integers that differ in signedness: the clear majority
				int best = 0;
				boolean tie = false;
				for (Map.Entry<String, Integer> e : counts.entrySet()) {
					if (e.getValue() > best) {
						best = e.getValue();
						chosen = distinct.get(e.getKey());
						tie = false;
					}
					else if (e.getValue() == best) {
						tie = true;
					}
				}
				if (tie) {
					return null;
				}
			}
		}
		// single bytes in firmware are numbers, not characters
		if (chosen instanceof Pointer pointer && pointer.getDataType() != null &&
			isChar(pointer.getDataType())) {
			return new PointerDataType(byteType(pointer.getDataType(), signedChar),
				pointer.getLength());
		}
		return isChar(chosen) ? byteType(chosen, signedChar) : chosen;
	}

	private static boolean isChar(DataType type) {
		return type instanceof CharDataType && type.getLength() == 1;
	}

	/** {@code byte} or {@code sbyte} for a character type */
	private static DataType byteType(DataType c, boolean signedChar) {
		boolean signed = c instanceof SignedCharDataType ||
			(!(c instanceof UnsignedCharDataType) && signedChar);
		return signed ? SignedByteDataType.dataType : ByteDataType.dataType;
	}

	static boolean applyType(Program program, Address addr, DataType type) {
		Listing listing = program.getListing();
		Data data = listing.getDefinedDataAt(addr);
		if (data == null || !Undefined.isUndefined(data.getDataType()) ||
			data.getLength() != type.getLength()) {
			return false;
		}
		try {
			listing.clearCodeUnits(addr, data.getMaxAddress(), false);
			listing.createData(addr, type);
			return true;
		}
		catch (CodeUnitInsertionException e) {
			try {
				listing.createData(addr, data.getDataType());
			}
			catch (CodeUnitInsertionException e2) {
				// the original undefined data could not be restored; leave the bytes
			}
			return false;
		}
	}
}
