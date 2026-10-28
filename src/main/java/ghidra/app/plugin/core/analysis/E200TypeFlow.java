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

import ghidra.app.plugin.core.analysis.E200Integers.Extension;
import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.pcode.*;
import ghidra.program.model.symbol.SourceType;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

/**
 * Types of the values that functions pass to each other (part of
 * {@link E200DataTypes}).
 * <p>
 * Decompiler Parameter ID commits the type the decompiler infers for a parameter or return
 * value from the function itself. A function that only copies a value, storing it, passing it
 * on or returning it, gives it no type, and the parameter stays {@code undefined4}. The type
 * is known where the value comes from or goes to: the callers pass a {@code float} or the
 * address of a {@code ushort}, the global it is stored in is an {@code int}.
 * <p>
 * The places that hold values, global data, parameters and return values, are linked where
 * the decompiled code copies a value from one to another: an argument that is a parameter of
 * the caller, a global or the result of another call; a returned value; a global assigned
 * one of these. Each group of linked places gets the type all the types seen for them agree
 * on, the same rules as for globals but without letting a {@code float} win over integers,
 * and the places of undefined type in the group get it where it fits: the same size, or a
 * pointer to a type of the size a pointer parameter's undefined target has.
 * <p>
 * Before that, a group whose values code uses as pointers to a structure, reading or writing
 * at constant offsets, gets a pointer to a structure of the fields it accesses (see
 * {@link E200Structures}), and a group whose values code calls through, or that get the
 * entry point of a function, a pointer to a function definition (see
 * {@link E200FunctionPointers.Definitions}): the definition of the functions where they are
 * known and agree, else one with the arguments of the calls.
 * <p>
 * Parameters and return values of one or two bytes arrive in a register of four, which
 * Decompiler Parameter ID gives them. The width that the uses of a value show (see
 * {@link E200Integers#width}) is resolved over the places the value is passed to or
 * returned from, and a parameter whose uses say nothing has the width of the values its
 * callers pass, when they all are small constants or values extended from a byte or
 * halfword.
 * <p>
 * Optionally, places whose group shows no type at all then get the unsigned integer of their
 * size ({@code byte}, {@code ushort}, {@code uint}), and pointers to undefined data of 1, 2
 * or 4 bytes a pointer to it. These values are only copied, compared for equality or
 * accessed in bytes, as the {@code uint8} buffers of AUTOSAR code are; a value that is
 * signed, a {@code float} or a pointer shows it in some use. A group in which any value is
 * a pointer, a {@code float} or a structure gets no default. Functions that return nothing
 * and whose result no caller reads get the return type {@code void}, which Decompiler
 * Parameter ID leaves undefined as it does not see the callers.
 * <p>
 * The work is in two parts: {@link #collect} gathers the {@link Facts} of one decompiled
 * function, and {@link #apply} types the places from the facts of all of them, in the order
 * above: pointers to structures, pointers to functions, types from values and defaults,
 * {@code void} returns, widths, signedness.
 */
final class E200TypeFlow {

	/** Rounds in which the widths of values passed on or returned are resolved */
	private static final int MAX_WIDTH_ROUNDS = 16;

	private E200TypeFlow() {
	}

	// ---- Places -------------------------------------------------------------------------------

	/**
	 * A place that holds a value: global data, a function's parameter, its return value.
	 * Places are ordered globals first, then parameters, then return values, by address: the
	 * order their groups are named after.
	 */
	sealed interface Slot extends Comparable<Slot> permits Global, Param, Return {

		/** The type of the place, or null if it is not there */
		DataType current(Program program);

		/** The function of a parameter or return value, or null */
		Function function(Program program);

		/** The address, or the function and index, the place is named after */
		String name();

		/** 0 for a global, 1 for a parameter, 2 for a return value */
		int rank();

		@Override
		default int compareTo(Slot other) {
			int c = Integer.compare(rank(), other.rank());
			return c != 0 ? c : name().compareTo(other.name());
		}
	}

	record Global(Address address) implements Slot {
		@Override
		public DataType current(Program program) {
			Data data = program.getListing().getDefinedDataAt(address);
			return data == null ? null : data.getDataType();
		}

		@Override
		public Function function(Program program) {
			return null;
		}

		@Override
		public String name() {
			return address.toString(false);
		}

		@Override
		public int rank() {
			return 0;
		}
	}

	record Param(Address entry, int index) implements Slot {
		@Override
		public DataType current(Program program) {
			Function f = function(program);
			return f != null && index < f.getParameterCount()
					? f.getParameter(index).getDataType()
					: null;
		}

		@Override
		public Function function(Program program) {
			return program.getFunctionManager().getFunctionAt(entry);
		}

		@Override
		public String name() {
			return entry.toString(false) + "_" + index;
		}

		@Override
		public int rank() {
			return 1;
		}
	}

	record Return(Address entry) implements Slot {
		@Override
		public DataType current(Program program) {
			Function f = function(program);
			return f == null ? null : f.getReturnType();
		}

		@Override
		public Function function(Program program) {
			return program.getFunctionManager().getFunctionAt(entry);
		}

		@Override
		public String name() {
			return entry.toString(false) + "_ret";
		}

		@Override
		public int rank() {
			return 2;
		}
	}

	// ---- Facts --------------------------------------------------------------------------------

	/**
	 * What one decompiled function shows: the types of values in places, informative or not,
	 * and the values it copies from one place to another.
	 */
	static final class Facts {
		final List<Map.Entry<Slot, DataType>> types = new ArrayList<>();
		final List<Map.Entry<Slot, Slot>> copies = new ArrayList<>();
		/** How the uses of the values of places show their signedness */
		final Map<Slot, Integer> signs = new HashMap<>();
		/** The width that the uses of parameters and of the results of calls show */
		final Map<Slot, Width> widths = new HashMap<>();
		/** The width of the value passed to a parameter at each call */
		final List<Map.Entry<Slot, Extension>> arguments = new ArrayList<>();
		/** The places that get a constant that is no address in memory: not only pointers */
		final Set<Slot> integers = new HashSet<>();
		/** What code does with the values of places used as pointers */
		final List<Map.Entry<Slot, E200Structures.Shape>> shapes = new ArrayList<>();
		/**
		 * The addresses of globals that are passed to places, as {@code f(&g)}: the places point
		 * to the data there
		 */
		final List<Map.Entry<Slot, Address>> pointees = new ArrayList<>();
		/** The entry points of functions that places get, as {@code p = f} or {@code g(f)} */
		final List<Map.Entry<Slot, Address>> functionTargets = new ArrayList<>();
		/** The places whose values code calls through, and the calls */
		final List<Map.Entry<Slot, E200FunctionPointers.Call>> calls = new ArrayList<>();
		/**
		 * The width of the value the function returns, if every return gives a value extended
		 * from a byte or halfword, with the signedness the extensions show; else null
		 */
		Extension returned;
		/** The function */
		Address entry;
		/** The function, if the decompiler sees no value returned by it */
		Address returnsNothing;
		/** The function, if its return type is not known yet (not set by Parameter ID) */
		Address returnUnknown;
		/** The functions whose results this one reads after calling them */
		final Set<Address> resultsRead = new HashSet<>();

		void type(Slot slot, DataType type) {
			if (type != null) {
				types.add(Map.entry(slot, type));
			}
		}

		/** Records the width the uses of the value in a place show, if they show anything. */
		void width(Slot slot, HighVariable variable, FunctionManager functions, Address entry) {
			Width width = E200Integers.width(variable, functions, entry);
			if (width.width > 0 || !width.deps.isEmpty()) {
				widths.computeIfAbsent(slot, s -> new Width()).merge(width);
			}
		}

		/** The globals the function uses */
		Set<Address> globals() {
			Set<Address> globals = new HashSet<>();
			for (Map.Entry<Slot, DataType> t : types) {
				if (t.getKey() instanceof Global g) {
					globals.add(g.address());
				}
			}
			return globals;
		}
	}

	/**
	 * The width of the value in a place that its uses show (see {@link E200Integers#width}):
	 * 1 or 2 if narrowed, 4 if a use needs the whole value, 0 if no use says; the signedness
	 * evidence of the narrowed values; and the places whose width the value also has, those
	 * it is passed to or returned from
	 */
	static final class Width {
		int width;
		int evidence;
		final Set<Slot> deps = new HashSet<>();

		void merge(int w, int e) {
			width = Math.max(width, w);
			evidence += e;
		}

		void merge(Width other) {
			merge(other.width, other.evidence);
			deps.addAll(other.deps);
		}
	}

	/**
	 * The places typed from the values passed to them, those given a default type, and the
	 * return values of functions that return nothing, typed {@code void}
	 */
	record Typed(List<Slot> fromValues, List<Slot> byDefault, List<Slot> voids) {
	}

	/** Collects the facts of a decompiled function. */
	static Facts collect(HighFunction high) {
		Facts facts = new Facts();
		Function function = high.getFunction();
		FunctionManager functions = function.getProgram().getFunctionManager();
		Address entry = function.getEntryPoint();
		facts.entry = entry;
		DataType returned = high.getFunctionPrototype().getReturnType();
		if (returned == null || returned instanceof VoidDataType) {
			facts.returnsNothing = entry;
		}
		else if (!(returned instanceof DefaultDataType)) {
			facts.type(new Return(entry), returned);
		}
		if (function.getReturnType() instanceof DefaultDataType) {
			facts.returnUnknown = entry; // Parameter ID did not decide
		}
		LocalSymbolMap locals = high.getLocalSymbolMap();
		for (int i = 0; i < locals.getNumParams(); i++) {
			HighSymbol param = locals.getParamSymbol(i);
			HighVariable variable = param.getHighVariable();
			if (variable != null) {
				Slot slot = new Param(entry, param.getCategoryIndex());
				facts.type(slot, E200Integers.of(variable));
				facts.signs.merge(slot, E200Integers.evidence(variable), Integer::sum);
				facts.width(slot, variable, functions, entry);
			}
		}
		Iterator<HighSymbol> globals = high.getGlobalSymbolMap().getSymbols();
		while (globals.hasNext()) {
			HighVariable variable = globals.next().getHighVariable();
			Slot global = variable == null ? null : global(variable.getRepresentative());
			if (global != null) {
				facts.type(global, E200Integers.of(variable));
				facts.signs.merge(global, E200Integers.evidence(variable), Integer::sum);
			}
		}
		int returns = 0;
		boolean allReturnsNarrow = true;
		Extension returnedWidth = null;
		Iterator<PcodeOpAST> ops = high.getPcodeOps();
		while (ops.hasNext()) {
			PcodeOpAST op = ops.next();
			switch (op.getOpcode()) {
				case PcodeOp.CALL -> {
					Function callee = E200Code.callee(functions, op);
					if (callee == null) {
						break;
					}
					Address target = callee.getEntryPoint();
					if (callee.getParameterCount() == op.getNumInputs() - 1) {
						for (int i = 1; i < op.getNumInputs(); i++) {
							Varnode argument = op.getInput(i);
							flow(facts, functions, entry, argument, new Param(target, i - 1));
							if (argument.getSize() == 4) {
								Extension extended = E200Integers.extended(argument, 0);
								facts.arguments.add(Map.entry(new Param(target, i - 1),
									extended == null ? Extension.WIDE : extended));
							}
						}
					}
					if (op.getOutput() != null) {
						facts.resultsRead.add(target);
						facts.type(new Return(target), type(op.getOutput()));
						facts.signs.merge(new Return(target),
							E200Integers.evidence(op.getOutput().getHigh()), Integer::sum);
						facts.width(new Return(target), op.getOutput().getHigh(), functions, entry);
						Slot global = global(op.getOutput()); // the result goes to a global
						if (global != null) {
							facts.copies.add(Map.entry(global, new Return(target)));
						}
					}
				}
				case PcodeOp.CALLIND -> {
					Slot called = source(functions, entry, E200Code.unwrap(op.getInput(0)), 0);
					if (called != null) {
						facts.calls.add(Map.entry(called, E200FunctionPointers.Call.of(op)));
					}
				}
				case PcodeOp.RETURN -> {
					if (op.getNumInputs() > 1) {
						flow(facts, functions, entry, op.getInput(1), new Return(entry));
						Extension narrow = E200Integers.extended(op.getInput(1), 0);
						if (narrow == null) {
							allReturnsNarrow = false;
						}
						else {
							returnedWidth =
								returnedWidth == null ? narrow : returnedWidth.widest(narrow);
						}
						returns++;
					}
				}
				case PcodeOp.COPY -> {
					Slot global = global(op.getOutput());
					if (global != null) {
						flow(facts, functions, entry, op.getInput(0), global);
					}
				}
				default -> {
					// no value moves between places
				}
			}
		}
		if (returns > 0 && allReturnsNarrow && returnedWidth != null && returnedWidth.narrow()) {
			facts.returned = returnedWidth;
		}
		E200Structures.collect(high, facts);
		return facts;
	}

	/** A value goes to {@code sink}: its type is one of the sink's, and it links its source. */
	private static void flow(Facts facts, FunctionManager functions, Address entry, Varnode value,
			Slot sink) {
		Program program = functions.getProgram();
		if (value != null && value.isConstant() && value.getSize() == 4 && value.getOffset() != 0 &&
			value.getOffset() != 0xffffffffL) { // all ones marks a pointer as not set too
			Address address = program.getAddressFactory()
					.getDefaultAddressSpace()
					.getTruncatedAddress(value.getOffset(), true);
			if (!program.getMemory().contains(address)) {
				facts.integers.add(sink);
			}
		}
		facts.type(sink, type(value));
		Slot source = source(functions, entry, value, 0);
		if (source != null && !source.equals(sink)) {
			facts.copies.add(Map.entry(sink, source));
		}
		Address pointee = E200Code.addressOf(program, value, 0);
		if (pointee != null) {
			if (functions.getFunctionAt(pointee) != null) {
				facts.functionTargets.add(Map.entry(sink, pointee));
			}
			else {
				facts.pointees.add(Map.entry(sink, pointee));
			}
		}
	}

	/** The place a value was copied from: a parameter, a global or a call's result, or null */
	private static Slot source(FunctionManager functions, Address entry, Varnode value,
			int depth) {
		if (value == null || value.isConstant()) {
			return null;
		}
		HighVariable high = value.getHigh();
		if (high instanceof HighParam param) {
			return new Param(entry, param.getSlot());
		}
		if (high instanceof HighGlobal) {
			return global(value);
		}
		PcodeOp def = value.getDef();
		if (def == null || depth > 4) {
			return null;
		}
		if (def.getOpcode() == PcodeOp.COPY) {
			return source(functions, entry, def.getInput(0), depth + 1);
		}
		if (def.getOpcode() == PcodeOp.CALL) {
			Function callee = E200Code.callee(functions, def);
			return callee == null ? null : new Return(callee.getEntryPoint());
		}
		return null;
	}

	/**
	 * The global a varnode holds, when it is all of a global symbol in memory: the varnode
	 * may be the memory itself or a register the decompiler merged with it
	 */
	private static Slot global(Varnode v) {
		if (v == null || !(v.getHigh() instanceof HighGlobal g)) {
			return null;
		}
		HighSymbol symbol = g.getSymbol();
		if (symbol == null || symbol.getStorage() == null ||
			!symbol.getStorage().isMemoryStorage() || symbol.getSize() != v.getSize()) {
			return null;
		}
		return new Global(symbol.getStorage().getMinAddress());
	}

	/** The type the decompiler gives a value, informative or not; null for constants */
	private static DataType type(Varnode v) {
		if (v == null || v.isConstant() || v.getHigh() == null) {
			return null;
		}
		if (v.getHigh() instanceof HighConstant) {
			DataType dt = v.getHigh().getDataType();
			return dt instanceof Pointer ? dt : null;
		}
		return E200Integers.of(v.getHigh());
	}

	// ---- Groups -------------------------------------------------------------------------------

	/**
	 * The places linked by the values that pass between them, as groups, with what the facts
	 * say about each group. The places that are passed the address of the same global point
	 * to data of one layout, so their groups are one group where their shapes fit together,
	 * and the data gets the group's structure.
	 */
	private static final class Groups {
		private final Map<Slot, Slot> parent = new HashMap<>();
		/** All the places */
		final Set<Slot> slots = new HashSet<>();
		/** The types seen for each place */
		final Map<Slot, List<DataType>> seen = new HashMap<>();
		/** The functions the decompiler sees returning nothing */
		final Set<Address> noReturns = new HashSet<>();
		/**
		 * The functions whose return values stay untyped: they return nothing, or it is not
		 * known whether they do and no decompiled caller reads the result, as with functions
		 * called only through pointers (a value they pass on says nothing about them)
		 */
		final Set<Address> untypedReturns = new HashSet<>();
		/** The groups that get constants other than addresses, by root */
		final Set<Slot> integers = new HashSet<>();
		/** The shapes of the groups whose values code uses as pointers, by root */
		final Map<Slot, E200Structures.Shape> shapes = new HashMap<>();
		/** The data each group points to, by root */
		final Map<Slot, Set<Address>> pointed = new HashMap<>();
		/** The globals pointed to by groups whose shapes do not fit together */
		final Set<Address> disputed = new HashSet<>();
		/** The types seen for the places of each group, by root */
		final Map<Slot, List<DataType>> types = new HashMap<>();
		/** The places of each group, by root */
		final Map<Slot, List<Slot>> members = new HashMap<>();
		/** The entry points of functions that the places of each group get, by root */
		final Map<Slot, Set<Address>> functionTargets = new HashMap<>();
		/** The calls through the values of each group, by root */
		final Map<Slot, List<E200FunctionPointers.Call>> calls = new HashMap<>();
		/** The signedness evidence of the uses of each group's values, by root */
		final Map<Slot, Integer> signs = new HashMap<>();

		/**
		 * @param facts the facts of the decompiled functions
		 * @param globalTypes the types of the uses of globals, as the analyzer collected them
		 */
		Groups(List<Facts> facts, Map<Address, List<DataType>> globalTypes, TaskMonitor monitor)
				throws CancelledException {
			globalTypes.forEach((a, types) -> seen.computeIfAbsent(new Global(a),
				s -> new ArrayList<>()).addAll(types));
			Set<Address> unknownReturns = new HashSet<>();
			Set<Address> read = new HashSet<>();
			for (Facts f : facts) {
				if (f.returnsNothing != null) {
					noReturns.add(f.returnsNothing);
				}
				if (f.returnUnknown != null) {
					unknownReturns.add(f.returnUnknown);
				}
				read.addAll(f.resultsRead);
				for (Map.Entry<Slot, DataType> t : f.types) {
					seen.computeIfAbsent(t.getKey(), s -> new ArrayList<>()).add(t.getValue());
				}
				for (Map.Entry<Slot, Slot> c : f.copies) {
					union(c.getKey(), c.getValue());
				}
			}
			unknownReturns.removeAll(read);
			untypedReturns.addAll(noReturns);
			untypedReturns.addAll(unknownReturns);
			slots.addAll(seen.keySet());
			slots.addAll(parent.keySet());
			slots.addAll(parent.values());
			Map<Address, Set<Slot>> pointees = new HashMap<>();
			for (Facts f : facts) {
				slots.addAll(f.signs.keySet());
				for (Slot s : f.integers) {
					integers.add(find(s));
				}
				for (Map.Entry<Slot, E200Structures.Shape> e : f.shapes) {
					slots.add(e.getKey());
					shapes.computeIfAbsent(find(e.getKey()), r -> new E200Structures.Shape())
							.merge(e.getValue());
				}
				for (Map.Entry<Slot, Address> e : f.pointees) {
					slots.add(e.getKey());
					pointees.computeIfAbsent(e.getValue(), a -> new LinkedHashSet<>())
							.add(e.getKey());
				}
				for (Map.Entry<Slot, Address> e : f.functionTargets) {
					slots.add(e.getKey());
				}
				for (Map.Entry<Slot, E200FunctionPointers.Call> e : f.calls) {
					slots.add(e.getKey());
				}
			}
			mergePointing(pointees, monitor);
			for (Slot s : slots) {
				Slot root = find(s);
				types.computeIfAbsent(root, r -> new ArrayList<>())
						.addAll(seen.getOrDefault(s, List.of()));
				members.computeIfAbsent(root, r -> new ArrayList<>()).add(s);
			}
			for (Facts f : facts) {
				for (Map.Entry<Slot, Address> e : f.functionTargets) {
					functionTargets.computeIfAbsent(find(e.getKey()), r -> new TreeSet<>())
							.add(e.getValue());
				}
				for (Map.Entry<Slot, E200FunctionPointers.Call> e : f.calls) {
					calls.computeIfAbsent(find(e.getKey()), r -> new ArrayList<>())
							.add(e.getValue());
				}
				f.signs.forEach((s, e) -> signs.merge(find(s), e, Integer::sum));
			}
		}

		/**
		 * Makes the groups that point to the same global one group where their shapes fit
		 * together, and records the data each group points to.
		 */
		private void mergePointing(Map<Address, Set<Slot>> pointees, TaskMonitor monitor)
				throws CancelledException {
			Map<Slot, Set<Address>> byFirst = new HashMap<>();
			for (Map.Entry<Address, Set<Slot>> e : pointees.entrySet()) {
				monitor.checkCancelled();
				Slot first = null;
				for (Slot s : e.getValue()) {
					Slot root = find(s);
					if (integers.contains(root)) {
						continue; // holds integers too: no structure, so nothing to share
					}
					if (first == null) {
						first = root;
						continue;
					}
					if (root.equals(first)) {
						continue;
					}
					E200Structures.Shape a =
						shapes.computeIfAbsent(first, r -> new E200Structures.Shape());
					E200Structures.Shape b =
						shapes.computeIfAbsent(root, r -> new E200Structures.Shape());
					if (!a.compatible(b)) {
						disputed.add(e.getKey());
						continue;
					}
					union(root, first); // first stays the root
					a.merge(b);
					shapes.remove(root);
				}
				if (first != null) {
					byFirst.computeIfAbsent(first, r -> new HashSet<>()).add(e.getKey());
				}
			}
			byFirst.forEach((s, addresses) -> pointed
					.computeIfAbsent(find(s), r -> new HashSet<>())
					.addAll(addresses));
		}

		Slot find(Slot s) {
			Slot root = s;
			for (Slot p = parent.get(root); p != null; p = parent.get(root)) {
				root = p;
			}
			while (!s.equals(root)) { // path compression
				s = parent.put(s, root);
			}
			return root;
		}

		/** Joins the groups of two places; the root of {@code b}'s group becomes the root */
		private void union(Slot a, Slot b) {
			Slot ra = find(a);
			Slot rb = find(b);
			if (!ra.equals(rb)) {
				parent.put(ra, rb);
			}
		}

		/** Whether the group of a place gets constants that are no addresses */
		boolean integer(Slot s) {
			return integers.contains(find(s));
		}

		/** The types seen for the places of the group of a place */
		List<DataType> types(Slot s) {
			return types.getOrDefault(find(s), List.of());
		}
	}

	/**
	 * Sets the types of places, where they are analysis' to set: a global whose uses were all
	 * decompiled, with data of the type's length, or a parameter or return value of a
	 * function whose callers were all decompiled, not a thunk, with a signature not set by the
	 * user or an import. A function not known to return a value gets no return type but
	 * {@code void}.
	 */
	private static final class Places {
		final Program program;
		/** The globals that may be typed, whose uses were all decompiled */
		final Set<Address> globals;
		/** The functions whose callers were all decompiled */
		final Set<Function> complete;
		final Set<Address> untypedReturns;

		Places(Program program, Set<Address> globals, Set<Function> complete,
				Set<Address> untypedReturns) {
			this.program = program;
			this.globals = globals;
			this.complete = complete;
			this.untypedReturns = untypedReturns;
		}

		/** Whether the signature of a function is analysis' to change */
		boolean settable(Function f) {
			return f != null && complete.contains(f) && !f.isThunk() &&
				!f.getSignatureSource().isHigherPriorityThan(SourceType.ANALYSIS);
		}

		/** Gives a place a type; returns whether it did */
		boolean set(Slot s, DataType type) {
			try {
				if (s instanceof Global g) {
					return globals.contains(g.address()) &&
						E200Data.replace(program.getListing(), g.address(), type);
				}
				Function f = s.function(program);
				if (!settable(f)) {
					return false;
				}
				if (s instanceof Param p) {
					if (p.index() >= f.getParameterCount()) {
						return false;
					}
					f.getParameter(p.index()).setDataType(type, SourceType.ANALYSIS);
					return true;
				}
				if (!(type instanceof VoidDataType) && untypedReturns.contains(f.getEntryPoint())) {
					return false;
				}
				f.setReturnType(type, SourceType.ANALYSIS);
				return true;
			}
			catch (InvalidInputException e) {
				Msg.warn(E200Analyzer.class, "Could not type " + s + ": " + e.getMessage());
				return false;
			}
		}
	}

	// ---- Typing -------------------------------------------------------------------------------

	/**
	 * Types the parameters, return values and globals of undefined type from the facts, and
	 * optionally gives the places whose group shows no type a default type.
	 *
	 * @param facts the facts of the decompiled functions
	 * @param globalTypes the types of the uses of globals, as the analyzer collected them
	 * @param globals the globals that may be typed, whose uses were all decompiled
	 * @param complete the functions whose callers were all decompiled, whose parameters and
	 * return values may be typed
	 * @param defaults whether to give default types
	 * @return the places typed
	 */
	static Typed apply(Program program, List<Facts> facts,
			Map<Address, List<DataType>> globalTypes, Set<Address> globals,
			Set<Function> complete, boolean defaults, TaskMonitor monitor)
			throws CancelledException {
		Groups groups = new Groups(facts, globalTypes, monitor);
		Places places = new Places(program, globals, complete, groups.untypedReturns);
		E200FunctionPointers.Definitions definitions =
			new E200FunctionPointers.Definitions(program);
		Typed typed = new Typed(new ArrayList<>(), new ArrayList<>(), new ArrayList<>());
		typeStructurePointers(groups, places, definitions, typed, monitor);
		typeFunctionPointers(groups, places, definitions, typed, monitor);
		typeFromValues(groups, places, defaults, typed, monitor);
		if (defaults) {
			typeVoidReturns(groups, places, typed);
		}
		Set<Slot> narrowed = narrow(facts, groups, places, typed, monitor);
		sign(groups, places, narrowed, typed, monitor);
		return typed;
	}

	/**
	 * Gives the places of the groups whose values code uses as pointers to a structure a
	 * pointer to the structure of the fields it accesses, and the data the groups point to
	 * the structure.
	 */
	private static void typeStructurePointers(Groups groups, Places places,
			E200FunctionPointers.Definitions definitions, Typed typed, TaskMonitor monitor)
			throws CancelledException {
		Program program = places.program;
		boolean signedChar = program.getDataTypeManager().getDataOrganization().isSignedChar();
		for (Map.Entry<Slot, E200Structures.Shape> e : groups.shapes.entrySet()) {
			monitor.checkCancelled();
			Slot root = e.getKey();
			E200Structures.Shape shape = e.getValue();
			if (pointsToComposite(groups.types(root)) || groups.integers.contains(root)) {
				continue;
			}
			Set<Address> instances = groups.pointed.getOrDefault(root, Set.of());
			// a value that the group's functions access as one word and other code accesses
			// in pieces is a structure of the pieces
			TreeMap<Long, DataType> pieces = pieces(program, instances, shape, signedChar);
			if (!shape.structure() && pieces.isEmpty()) {
				continue;
			}
			List<Slot> group = groups.members.get(root);
			Pointer pointer = structurePointer(program, definitions, group, shape, signedChar,
				spacing(instances), pieces);
			if (pointer == null) {
				continue;
			}
			for (Slot s : group) {
				if (E200Structures.replaceable(s.current(program)) && places.set(s, pointer)) {
					typed.fromValues().add(s);
				}
			}
			for (Address a : instances) {
				if (places.globals.contains(a) && !groups.disputed.contains(a) &&
					E200Data.structureAt(program, a, (Structure) pointer.getDataType())) {
					typed.fromValues().add(new Global(a));
				}
			}
		}
	}

	/**
	 * Gives the places of the groups whose values code calls through, or that get the entry
	 * point of a function, a pointer to a function definition, unless they are dereferenced
	 * too (a copy routine gets the address of code as a source). The groups are typed in
	 * their order, so that the definitions get the same names at every analysis.
	 */
	private static void typeFunctionPointers(Groups groups, Places places,
			E200FunctionPointers.Definitions definitions, Typed typed, TaskMonitor monitor)
			throws CancelledException {
		Program program = places.program;
		Set<Slot> callable = new TreeSet<>(groups.functionTargets.keySet());
		callable.addAll(groups.calls.keySet());
		for (Slot root : callable) {
			monitor.checkCancelled();
			List<Slot> group = groups.members.get(root);
			if (group == null || pointsToComposite(groups.types(root)) ||
				groups.integers.contains(root) || groups.shapes.containsKey(root)) {
				continue;
			}
			Set<Address> targets = new TreeSet<>(groups.functionTargets.getOrDefault(root, Set.of()));
			for (Slot s : group) {
				if (s instanceof Global g) { // a pointer in flash: what it points to
					Data data = program.getListing().getDefinedDataAt(g.address());
					MemoryBlock block = program.getMemory().getBlock(g.address());
					List<Function> held = data == null || block == null || !block.isInitialized()
							? null
							: E200FunctionPointers.target(program.getFunctionManager(), data,
								new ArrayList<>());
					if (held != null) {
						held.forEach(f -> targets.add(f.getEntryPoint()));
					}
				}
			}
			FunctionDefinition definition =
				definitions.of(targets, groups.calls.getOrDefault(root, List.of()));
			if (definition == null) {
				continue;
			}
			Pointer pointer = new PointerDataType(definition, 4, program.getDataTypeManager());
			for (Slot s : group) {
				if (E200Structures.replaceable(s.current(program)) && places.set(s, pointer)) {
					typed.fromValues().add(s);
				}
			}
		}
	}

	/**
	 * Gives the places of undefined type the type their own uses, else their group, agree
	 * on; with {@code defaults}, those whose group shows no type get the unsigned integer of
	 * their size.
	 */
	private static void typeFromValues(Groups groups, Places places, boolean defaults,
			Typed typed, TaskMonitor monitor) throws CancelledException {
		Program program = places.program;
		boolean signedChar = program.getDataTypeManager().getDataOrganization().isSignedChar();
		for (Slot s : groups.slots) {
			monitor.checkCancelled();
			if (s instanceof Return r && groups.untypedReturns.contains(r.entry())) {
				continue;
			}
			List<DataType> group = groups.types(s);
			// a place that gets a constant that is no address, as an error code, holds no
			// pointer, whatever a caller that passes an address shows
			boolean integer = groups.integer(s);
			DataType type = E200Types.chooseType(
				informativeOnly(groups.seen.getOrDefault(s, List.of()), integer), signedChar,
				false, defaults);
			if (type == null) {
				type = E200Types.chooseType(informativeOnly(group, integer), signedChar, false,
					defaults);
			}
			List<Slot> list = typed.fromValues();
			if (type == null) {
				if (!defaults || group.stream().anyMatch(E200Types::informative)) {
					continue;
				}
				type = defaultType(s.current(program), group);
				list = typed.byDefault();
			}
			if (type != null && acceptsValue(s, s.current(program), type) && places.set(s, type)) {
				list.add(s);
			}
		}
	}

	/**
	 * Whether a place of type {@code current} may get {@code type} from the values passed to
	 * it: undefined data, a parameter of undefined type or pointing to undefined data that
	 * the type fits, or a return value that is not known or that the type fits
	 */
	private static boolean acceptsValue(Slot s, DataType current, DataType type) {
		if (s instanceof Global) {
			return current != null && Undefined.isUndefined(current);
		}
		if (s instanceof Param) {
			return E200Types.fits(current, type);
		}
		if (type instanceof VoidDataType) {
			return current instanceof DefaultDataType || Undefined.isUndefined(current);
		}
		return current instanceof DefaultDataType || E200Types.fits(current, type);
	}

	/**
	 * Gives the functions whose return values stay untyped the return type {@code void}:
	 * Decompiler Parameter ID leaves the return type of a function that returns nothing
	 * undefined, since it does not know whether a caller uses a result, and a function whose
	 * undefined result no decompiled caller reads returns nothing too.
	 */
	private static void typeVoidReturns(Groups groups, Places places, Typed typed) {
		for (Address entry : groups.untypedReturns) {
			Return r = new Return(entry);
			if (acceptsValue(r, r.current(places.program), VoidDataType.dataType) &&
				places.set(r, VoidDataType.dataType)) {
				typed.voids().add(r);
			}
		}
	}

	/** The widths of the values the callers of a function pass to one of its parameters */
	private static final class Arguments {
		/** The widest */
		int width;
		/** The signedness the extensions show */
		int evidence;
		/** How many values are extended from a byte or halfword */
		int extended;

		void add(Extension e) {
			width = Math.max(width, e.width());
			evidence += e.evidence();
			extended += e.narrow() ? 1 : 0;
		}

		/**
		 * The width the arguments give a parameter whose uses say nothing: 1 or 2 when all
		 * of them are small constants or values extended from that many bytes, and one is
		 * extended; else 0
		 */
		int width() {
			return width >= 1 && width <= 2 && extended > 0 ? width : 0;
		}
	}

	/**
	 * Gives the parameters and return values of one or two bytes that arrive in a register
	 * of four the integer of their width: the width their uses show, and for a value passed
	 * on or returned, that of the place it goes to. Returns the places narrowed.
	 */
	private static Set<Slot> narrow(List<Facts> facts, Groups groups, Places places,
			Typed typed, TaskMonitor monitor) throws CancelledException {
		Program program = places.program;
		Map<Slot, Width> widths = new HashMap<>();
		for (Facts f : facts) {
			f.widths.forEach((s, w) -> widths.computeIfAbsent(s, k -> new Width()).merge(w));
		}
		// a function that returns a value extended from a byte or halfword on every path
		// returns one, whatever its callers do with the register; their uses add signedness
		for (Facts f : facts) {
			if (f.returned != null && f.entry != null) {
				Slot r = new Return(f.entry);
				Width callers = widths.get(r);
				Width own = new Width();
				own.merge(f.returned.width(),
					f.returned.evidence() + (callers == null ? 0 : callers.evidence));
				widths.put(r, own);
			}
		}
		// a parameter whose uses say nothing, as one the function ignores, or only passes on
		// to such a parameter, has the width of the values its callers pass
		Map<Slot, Arguments> arguments = new HashMap<>();
		for (Facts f : facts) {
			for (Map.Entry<Slot, Extension> e : f.arguments) {
				arguments.computeIfAbsent(e.getKey(), s -> new Arguments()).add(e.getValue());
			}
		}
		// The width of each place: its own uses, those of the places its value goes to, and
		// where those say nothing, its callers' arguments. A place that stays four bytes wide
		// makes the values passed to it four bytes wide: the call passes the whole register.
		Set<Slot> all = new HashSet<>(widths.keySet());
		all.addAll(arguments.keySet());
		Map<Slot, Integer> resolved = new HashMap<>();
		for (Slot s : all) {
			resolved.put(s, 0);
		}
		for (int round = 0; round < MAX_WIDTH_ROUNDS; round++) {
			monitor.checkCancelled();
			boolean changed = false;
			for (Slot s : all) {
				Width w = widths.get(s);
				int v = w == null ? 0 : w.width;
				if (w != null) {
					for (Slot dep : w.deps) {
						v = Math.max(v, width(dep, resolved, places));
					}
				}
				if (v == 0) {
					Arguments a = arguments.get(s);
					if (a != null) {
						v = a.width();
					}
				}
				if (v != resolved.get(s)) {
					resolved.put(s, v);
					changed = true;
				}
			}
			if (!changed) {
				break;
			}
		}
		Set<Slot> narrowed = new HashSet<>();
		for (Slot s : all) {
			int width = resolved.get(s);
			if (width == 0 || width > 2 || !narrowable(s, places)) {
				continue;
			}
			narrowed.add(s);
			Width w = widths.get(s);
			Arguments a = arguments.get(s);
			int evidence = (w == null ? 0 : w.evidence) + (a == null ? 0 : a.evidence);
			DataType type = E200Types.withSign(E200Types.unsigned(width), evidence);
			if (places.set(s, type)) {
				typed.fromValues().add(s);
			}
		}
		return narrowed;
	}

	/**
	 * The width of the value in a place that a value is passed to or returned from: that of
	 * its type if it is a byte or halfword already, else the width its own uses and callers
	 * give it if that can be set, or 4 if there is no such place or it stays four bytes
	 * wide, when the whole register is passed to it
	 */
	private static int width(Slot dep, Map<Slot, Integer> resolved, Places places) {
		DataType current = dep.current(places.program);
		if (current == null) {
			return 4;
		}
		if (current.getLength() <= 2 && (E200Types.integer(current) ||
			Undefined.isUndefined(current) && !(current instanceof DefaultDataType))) {
			return current.getLength();
		}
		Integer w = resolved.get(dep);
		if (w == null || w == 0 || w > 2 || !narrowable(dep, places)) {
			return 4;
		}
		return w;
	}

	/**
	 * Whether a place of four bytes may be narrowed: it is a parameter or return value whose
	 * type is an integer or undefined that analysis may set, and not the return value of a
	 * function not known to return anything
	 */
	private static boolean narrowable(Slot s, Places places) {
		DataType current = s.current(places.program);
		if (current == null || current.getLength() != 4 || current instanceof TypeDef ||
			!E200Types.integer(current) && !Undefined.isUndefined(current) ||
			s instanceof Global ||
			s instanceof Return r && places.untypedReturns.contains(r.entry())) {
			return false;
		}
		return places.settable(s.function(places.program));
	}

	/**
	 * Gives the integers analysis typed the signedness of the uses of their group, apart from
	 * the places just narrowed, which have it already.
	 */
	private static void sign(Groups groups, Places places, Set<Slot> narrowed, Typed typed,
			TaskMonitor monitor) throws CancelledException {
		for (Slot s : groups.slots) {
			monitor.checkCancelled();
			DataType current = s.current(places.program);
			if (!E200Types.integer(current) || current instanceof TypeDef ||
				narrowed.contains(s) ||
				s instanceof Return r && groups.untypedReturns.contains(r.entry())) {
				continue;
			}
			DataType type =
				E200Types.withSign(current, groups.signs.getOrDefault(groups.find(s), 0));
			if (!type.isEquivalent(current) && places.set(s, type)) {
				typed.fromValues().add(s);
			}
		}
	}

	// ---- Structures ---------------------------------------------------------------------------

	/**
	 * A pointer to the structure of a group, named after its first global, else the first
	 * parameter or return value; null if the shape gives no fields
	 */
	private static Pointer structurePointer(Program program,
			E200FunctionPointers.Definitions definitions, List<Slot> group,
			E200Structures.Shape shape, boolean signedChar, long limit,
			TreeMap<Long, DataType> pieces) {
		DataTypeManager manager = program.getDataTypeManager();
		String name = "P_" + Collections.min(group).name();
		DataType existing = manager.getDataType(E200Types.CATEGORY, name);
		Structure built = E200Structures.build(program, definitions, shape, name, signedChar, 0,
			limit, pieces);
		if (existing instanceof Structure s) {
			// built in an earlier round, from less of the code
			if (built != null) {
				E200Structures.refine(manager, s, built);
			}
		}
		else if (built == null) {
			return null;
		}
		else {
			existing = manager.addDataType(built, DataTypeConflictHandler.DEFAULT_HANDLER);
		}
		return new PointerDataType(existing, 4, manager);
	}

	/**
	 * The pieces of the fields of a shape that the data at the structure's instances shows:
	 * where code passes the address of a {@code byte} to a function that writes a
	 * {@code ushort} there, as a value and its complement, the field is the byte and what
	 * follows it, and the function writes the structure as a whole. By offset in the
	 * structure, the type of the smaller data at it, when the instances agree.
	 */
	private static TreeMap<Long, DataType> pieces(Program program, Set<Address> instances,
			E200Structures.Shape shape, boolean signedChar) {
		TreeMap<Long, DataType> pieces = new TreeMap<>();
		if (instances.isEmpty() || shape.fields.isEmpty()) {
			return pieces;
		}
		Listing listing = program.getListing();
		Map<Long, List<DataType>> found = new HashMap<>(); // by offset, the data of all instances
		for (Address instance : instances) {
			for (Map.Entry<Long, E200Structures.Field> e : shape.fields.entrySet()) {
				long offset = e.getKey();
				int size = e.getValue().size();
				if (size <= 1) {
					continue;
				}
				try {
					Address start = instance.addNoWrap(offset);
					Address end = start.addNoWrap(size - 1);
					for (Data d : listing.getDefinedData(new AddressSet(start, end), true)) {
						if (d.getLength() < size && d.getMaxAddress().compareTo(end) <= 0 &&
							E200Types.primitive(d.getDataType()) &&
							!Undefined.isUndefined(d.getDataType())) {
							found.computeIfAbsent(offset + d.getAddress().subtract(start),
								o -> new ArrayList<>()).add(d.getDataType());
						}
					}
				}
				catch (AddressOverflowException ex) {
					// no such instance
				}
			}
		}
		for (Map.Entry<Long, List<DataType>> e : found.entrySet()) {
			List<Integer> sizes = e.getValue().stream().map(DataType::getLength).toList();
			int size = E200Types.mostFrequent(sizes);
			DataType type = E200Types.chooseType(
				e.getValue().stream().filter(t -> t.getLength() == size).toList(), signedChar,
				true, true);
			pieces.put(e.getKey(), type != null ? type : Undefined.getUndefinedDataType(size));
		}
		// pieces that overlap each other, where the instances disagree, say nothing
		long end = -1;
		for (Iterator<Map.Entry<Long, DataType>> it = pieces.entrySet().iterator(); it
				.hasNext();) {
			Map.Entry<Long, DataType> e = it.next();
			if (e.getKey() < end) {
				it.remove();
			}
			else {
				end = e.getKey() + e.getValue().getLength();
			}
		}
		return pieces;
	}

	/**
	 * How far apart the instances of a structure that code passes by address are at the
	 * least, which bounds the structure's length: no instance holds another; 0 if there are
	 * fewer than two
	 */
	private static long spacing(Set<Address> instances) {
		List<Address> sorted = new ArrayList<>(instances);
		Collections.sort(sorted);
		long spacing = 0;
		for (int i = 1; i < sorted.size(); i++) {
			long gap = sorted.get(i).subtract(sorted.get(i - 1));
			if (gap > 0 && (spacing == 0 || gap < spacing)) {
				spacing = gap;
			}
		}
		return spacing;
	}

	/** Whether a group has a pointer to a structure, union or array of its own */
	private static boolean pointsToComposite(List<DataType> group) {
		for (DataType t : group) {
			if (t instanceof Pointer p && p.getDataType() instanceof Composite c &&
				!E200Types.ownStructure(c)) {
				return true;
			}
		}
		return false;
	}

	// ---- Types of places ----------------------------------------------------------------------

	/** The informative types, without the pointers if the place holds integers too */
	private static List<DataType> informativeOnly(List<DataType> types, boolean noPointers) {
		return types.stream()
				.filter(t -> E200Types.informative(t) && !(noPointers && t instanceof Pointer))
				.toList();
	}

	/**
	 * The default type of a place of undefined type whose group shows no type: the unsigned
	 * integer of its size, or a pointer to it for a pointer to undefined data, if no value in
	 * the group is anything else.
	 */
	private static DataType defaultType(DataType current, List<DataType> group) {
		if (current == null) {
			return null;
		}
		if (current instanceof Pointer pointer) {
			DataType target = pointer.getDataType();
			if (target == null) {
				return null;
			}
			DataType unsignedTarget =
				target instanceof Pointer p ? defaultType(p, group) : unsigned(target);
			if (unsignedTarget == null) {
				return null;
			}
			for (DataType t : group) {
				if (t instanceof Pointer p) {
					if (p.getDataType() == null || !E200Types.fits(p.getDataType(), unsignedTarget)) {
						return null;
					}
				}
				else if (!Undefined.isUndefined(t) || t.getLength() != pointer.getLength()) {
					return null;
				}
			}
			return new PointerDataType(unsignedTarget, pointer.getLength());
		}
		DataType unsigned = unsigned(current);
		if (unsigned == null) {
			return null;
		}
		for (DataType t : group) {
			if (t instanceof Pointer p) {
				if (current.getLength() != p.getLength()) {
					return null;
				}
			}
			else if (!Undefined.isUndefined(t) || t.getLength() != current.getLength()) {
				return null;
			}
		}
		return unsigned;
	}

	/** The unsigned integer of the size of undefined data of 1, 2, 4 or 8 bytes, or null */
	private static DataType unsigned(DataType undefined) {
		if (!Undefined.isUndefined(undefined) || undefined instanceof DefaultDataType) {
			return null;
		}
		return E200Types.unsigned(undefined.getLength());
	}

	/**
	 * Whether a place may still get a type: it is of undefined type, or a pointer to
	 * undefined data (a return value of DEFAULT type is not known to exist)
	 */
	static boolean open(Program program, Slot s) {
		return isOpen(s.current(program));
	}

	private static boolean isOpen(DataType current) {
		if (current == null || current instanceof DefaultDataType) {
			return false;
		}
		if (Undefined.isUndefined(current)) {
			return true;
		}
		if (current instanceof Pointer p) {
			return p.getDataType() != null && isOpen(p.getDataType());
		}
		return false;
	}
}
