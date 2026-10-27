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

import ghidra.program.model.address.Address;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.util.CodeUnitInsertionException;
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
 * {@link E200Structures}).
 * <p>
 * Optionally, places whose group shows no type at all then get the unsigned integer of their
 * size ({@code byte}, {@code ushort}, {@code uint}), and pointers to undefined data of 1, 2
 * or 4 bytes a pointer to it. These values are only copied, compared for equality or
 * accessed in bytes, as the {@code uint8} buffers of AUTOSAR code are; a value that is
 * signed, a {@code float} or a pointer shows it in some use. A group in which any value is
 * a pointer, a {@code float} or a structure gets no default. Functions that return nothing
 * and whose result no caller reads get the return type {@code void}, which Decompiler
 * Parameter ID leaves undefined as it does not see the callers.
 */
final class E200TypeFlow {

	private E200TypeFlow() {
	}

	/** A place that holds a value: global data, a function's parameter, its return value */
	sealed interface Slot permits Global, Param, Return {
	}

	record Global(Address address) implements Slot {
	}

	record Param(Address function, int index) implements Slot {
	}

	record Return(Address function) implements Slot {
	}

	/**
	 * What one decompiled function shows: the types of values in places, informative or not,
	 * and the values it copies from one place to another.
	 */
	static final class Facts {
		final List<Map.Entry<Slot, DataType>> types = new ArrayList<>();
		final List<Map.Entry<Slot, Slot>> copies = new ArrayList<>();
		/** How the uses of the values of places show their signedness */
		final Map<Slot, Integer> signs = new HashMap<>();
		/**
		 * The width that the uses of parameters and of the results of calls show (1 or 2 if
		 * they are only used masked or truncated to it, else 4), and the signedness evidence of
		 * the narrowed values
		 */
		final Map<Slot, int[]> widths = new HashMap<>();
		/** The places that get a constant that is no address in memory: not only pointers */
		final Set<Slot> integers = new HashSet<>();
		/** What code does with the values of places used as pointers */
		final List<Map.Entry<Slot, E200Structures.Shape>> shapes = new ArrayList<>();
		/** The function, if the decompiler sees no value returned by it */
		Address returnsNothing;

		void type(Slot slot, DataType type) {
			if (type != null) {
				types.add(Map.entry(slot, type));
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
		DataType returned = high.getFunctionPrototype().getReturnType();
		if (returned == null || returned instanceof VoidDataType) {
			facts.returnsNothing = entry;
		}
		else if (!(returned instanceof DefaultDataType)) {
			facts.type(new Return(entry), returned);
		}
		LocalSymbolMap locals = high.getLocalSymbolMap();
		for (int i = 0; i < locals.getNumParams(); i++) {
			HighSymbol param = locals.getParamSymbol(i);
			HighVariable variable = param.getHighVariable();
			if (variable != null) {
				Slot slot = new Param(entry, param.getCategoryIndex());
				facts.type(slot, E200Integers.of(variable));
				facts.signs.merge(slot, E200Integers.evidence(variable), Integer::sum);
				int[] narrowed = new int[1];
				int width = E200Integers.width(variable, narrowed);
				if (width > 0) {
					facts.widths.merge(slot, new int[] { width, narrowed[0] },
						E200TypeFlow::widest);
				}
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
		Iterator<PcodeOpAST> ops = high.getPcodeOps();
		while (ops.hasNext()) {
			PcodeOpAST op = ops.next();
			switch (op.getOpcode()) {
				case PcodeOp.CALL -> {
					Function callee = callee(functions, op);
					if (callee == null) {
						break;
					}
					Address target = callee.getEntryPoint();
					if (callee.getParameterCount() == op.getNumInputs() - 1) {
						for (int i = 1; i < op.getNumInputs(); i++) {
							flow(facts, functions, entry, op.getInput(i), new Param(target, i - 1));
						}
					}
					if (op.getOutput() != null) {
						facts.type(new Return(target), type(op.getOutput()));
						facts.signs.merge(new Return(target),
							E200Integers.evidence(op.getOutput().getHigh()), Integer::sum);
						int[] narrowed = new int[1];
						int width = E200Integers.width(op.getOutput().getHigh(), narrowed);
						if (width > 0) {
							facts.widths.merge(new Return(target),
								new int[] { width, narrowed[0] }, E200TypeFlow::widest);
						}
						Slot global = global(op.getOutput()); // the result goes to a global
						if (global != null) {
							facts.copies.add(Map.entry(global, new Return(target)));
						}
					}
				}
				case PcodeOp.RETURN -> {
					if (op.getNumInputs() > 1) {
						flow(facts, functions, entry, op.getInput(1), new Return(entry));
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
		E200Structures.collect(high, facts);
		return facts;
	}

	/** A value goes to {@code sink}: its type is one of the sink's, and it links its source. */
	private static void flow(Facts facts, FunctionManager functions, Address entry, Varnode value,
			Slot sink) {
		if (value != null && value.isConstant() && value.getSize() == 4 && value.getOffset() != 0) {
			Program program = functions.getProgram();
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
			Function callee = callee(functions, def);
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

	/** The function a call goes to, past thunks, or null */
	static Function callee(FunctionManager functions, PcodeOp call) {
		Varnode target = call.getInput(0);
		if (target == null || !target.isAddress()) {
			return null;
		}
		Function f = functions.getFunctionAt(target.getAddress());
		if (f != null && f.isThunk()) {
			f = f.getThunkedFunction(true);
		}
		return f == null || f.isExternal() ? null : f;
	}

	/** The type the decompiler gives a value, informative or not; null for constants */
	private static DataType type(Varnode v) {
		if (v == null || v.isConstant() || v.getHigh() == null) {
			return null;
		}
		if (v.getHigh() instanceof HighConstant) {
			DataType dt = v.getHigh().getDataType();
			if (dt instanceof Pointer) {
				return dt;
			}
			return null;
		}
		return E200Integers.of(v.getHigh());
	}

	/** Whether the type says more than its size */
	static boolean informative(DataType type) {
		if (type == null || Undefined.isUndefined(type) || type instanceof VoidDataType) {
			return false;
		}
		if (type instanceof Pointer pointer) {
			DataType target = pointer.getDataType();
			return target != null && informative(target);
		}
		return true;
	}

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
		Map<Slot, List<DataType>> seen = new HashMap<>(); // all types seen
		Map<Slot, Slot> parent = new HashMap<>();
		globalTypes.forEach((a, types) -> seen.computeIfAbsent(new Global(a),
			s -> new ArrayList<>()).addAll(types));
		Set<Address> noReturns = new HashSet<>();
		for (Facts f : facts) {
			if (f.returnsNothing != null) {
				noReturns.add(f.returnsNothing);
			}
			for (Map.Entry<Slot, DataType> t : f.types) {
				seen.computeIfAbsent(t.getKey(), s -> new ArrayList<>()).add(t.getValue());
			}
			for (Map.Entry<Slot, Slot> c : f.copies) {
				union(parent, c.getKey(), c.getValue());
			}
		}
		Set<Slot> slots = new HashSet<>(seen.keySet());
		slots.addAll(parent.keySet());
		slots.addAll(parent.values());
		for (Facts f : facts) {
			slots.addAll(f.signs.keySet());
		}
		Set<Slot> integers = new HashSet<>(); // groups that get constants other than addresses
		for (Facts f : facts) {
			for (Slot s : f.integers) {
				integers.add(find(parent, s));
			}
		}
		Map<Slot, E200Structures.Shape> shapes = new HashMap<>(); // by group
		for (Facts f : facts) {
			for (Map.Entry<Slot, E200Structures.Shape> e : f.shapes) {
				slots.add(e.getKey());
				shapes.computeIfAbsent(find(parent, e.getKey()), r -> new E200Structures.Shape())
						.merge(e.getValue());
			}
		}
		Map<Slot, List<DataType>> groups = new HashMap<>();
		Map<Slot, List<Slot>> members = new HashMap<>();
		for (Slot s : slots) {
			groups.computeIfAbsent(find(parent, s), r -> new ArrayList<>())
					.addAll(seen.getOrDefault(s, List.of()));
			members.computeIfAbsent(find(parent, s), r -> new ArrayList<>()).add(s);
		}
		boolean signedChar = program.getDataTypeManager().getDataOrganization().isSignedChar();
		Typed typed = new Typed(new ArrayList<>(), new ArrayList<>(), new ArrayList<>());
		// pointers to structures, before the types of single values
		for (Map.Entry<Slot, E200Structures.Shape> e : shapes.entrySet()) {
			monitor.checkCancelled();
			if (!e.getValue().structure() || pointsToComposite(groups.get(e.getKey())) ||
				integers.contains(e.getKey())) {
				continue;
			}
			List<Slot> group = members.get(e.getKey());
			Pointer pointer = structurePointer(program, group, e.getValue(), signedChar);
			if (pointer == null) {
				continue;
			}
			for (Slot s : group) {
				if (setPointer(program, s, pointer, globals, complete, noReturns)) {
					typed.fromValues().add(s);
				}
			}
		}
		for (Slot s : slots) {
			monitor.checkCancelled();
			if (s instanceof Return r && noReturns.contains(r.function())) {
				continue;
			}
			List<DataType> group = groups.get(find(parent, s));
			DataType type = E200DataTypes.chooseType(
				informativeOnly(seen.getOrDefault(s, List.of())), signedChar, false, defaults);
			if (type == null) {
				type = E200DataTypes.chooseType(informativeOnly(group), signedChar, false, defaults);
			}
			List<Slot> list = typed.fromValues();
			if (type == null) {
				if (!defaults || group.stream().anyMatch(E200TypeFlow::informative)) {
					continue;
				}
				type = defaultType(current(program, s), group);
				list = typed.byDefault();
			}
			if (type != null && set(program, s, type, globals, complete, noReturns)) {
				list.add(s);
			}
		}
		if (defaults) {
			// Decompiler Parameter ID leaves the return type of a function that returns
			// nothing undefined, since it does not know whether a caller uses a result
			for (Address entry : noReturns) {
				Slot r = new Return(entry);
				if (set(program, r, VoidDataType.dataType, globals, complete, noReturns)) {
					typed.voids().add(r);
				}
			}
		}
		// parameters and return values of one or two bytes in a register of four
		Map<Slot, int[]> widths = new HashMap<>();
		for (Facts f : facts) {
			f.widths.forEach((s, w) -> widths.merge(s, w, E200TypeFlow::widest));
		}
		Set<Slot> narrowed = new HashSet<>();
		for (Map.Entry<Slot, int[]> e : widths.entrySet()) {
			Slot s = e.getKey();
			DataType current = current(program, s);
			if (e.getValue()[0] > 2 || current == null || current.getLength() != 4 ||
				current instanceof TypeDef ||
				!E200Integers.integer(current) && !Undefined.isUndefined(current) ||
				s instanceof Return r && noReturns.contains(r.function())) {
				continue;
			}
			narrowed.add(s);
			DataType type = E200Integers.withSign(E200DataTypes.unsigned(e.getValue()[0]),
				e.getValue()[1]);
			if (setInteger(program, s, type, globals, complete)) {
				typed.fromValues().add(s);
			}
		}
		// the signedness of the integers analysis typed, from the uses of their group
		Map<Slot, Integer> signs = new HashMap<>();
		for (Facts f : facts) {
			f.signs.forEach((s, e) -> signs.merge(find(parent, s), e, Integer::sum));
		}
		for (Slot s : slots) {
			monitor.checkCancelled();
			DataType current = current(program, s);
			if (!E200Integers.integer(current) || current instanceof TypeDef ||
				narrowed.contains(s) || s instanceof Return r && noReturns.contains(r.function())) {
				continue;
			}
			DataType type =
				E200Integers.withSign(current, signs.getOrDefault(find(parent, s), 0));
			if (!type.isEquivalent(current) && setInteger(program, s, type, globals, complete)) {
				typed.fromValues().add(s);
			}
		}
		return typed;
	}

	/** The wider of two widths, with the signedness evidence of both */
	private static int[] widest(int[] a, int[] b) {
		return new int[] { Math.max(a[0], b[0]), a[1] + b[1] };
	}

	/** Whether a group has a pointer to a structure, union or array of its own */
	private static boolean pointsToComposite(List<DataType> group) {
		for (DataType t : group) {
			if (t instanceof Pointer p && p.getDataType() instanceof Composite c &&
				!c.getCategoryPath().equals(E200Tables.CATEGORY)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * A pointer to the structure of a group, named after its first global, else the first
	 * parameter or return value; null if the shape gives no fields
	 */
	private static Pointer structurePointer(Program program, List<Slot> group,
			E200Structures.Shape shape, boolean signedChar) {
		Slot first = null;
		for (Slot s : group) {
			if (first == null || rank(s) < rank(first) ||
				rank(s) == rank(first) && name(s).compareTo(name(first)) < 0) {
				first = s;
			}
		}
		DataTypeManager manager = program.getDataTypeManager();
		String name = "P_" + name(first);
		DataType existing = manager.getDataType(E200Tables.CATEGORY, name);
		if (!(existing instanceof Structure)) {
			Structure built = E200Structures.build(manager, shape, name, signedChar, 0);
			if (built == null) {
				return null;
			}
			existing = manager.addDataType(built, DataTypeConflictHandler.DEFAULT_HANDLER);
		}
		return new PointerDataType(existing, 4, manager);
	}

	private static int rank(Slot s) {
		return s instanceof Global ? 0 : s instanceof Param ? 1 : 2;
	}

	private static String name(Slot s) {
		if (s instanceof Global g) {
			return g.address().toString(false);
		}
		if (s instanceof Param p) {
			return p.function().toString(false) + "_" + p.index();
		}
		return ((Return) s).function().toString(false) + "_ret";
	}

	/**
	 * Gives a place that holds an integer or a pointer to a single value, as analysis typed
	 * it, a pointer to a structure; returns whether it did
	 */
	private static boolean setPointer(Program program, Slot s, Pointer pointer,
			Set<Address> globals, Set<Function> complete, Set<Address> noReturns) {
		DataType current = current(program, s);
		if (!E200Structures.replaceable(current)) {
			return false;
		}
		try {
			if (s instanceof Global g) {
				Data data = program.getListing().getDefinedDataAt(g.address());
				if (!globals.contains(g.address()) || data == null) {
					return false;
				}
				program.getListing().clearCodeUnits(g.address(), data.getMaxAddress(), false);
				program.getListing().createData(g.address(), pointer);
				return true;
			}
			Function f = function(program, s);
			if (f == null || !complete.contains(f) || f.isThunk() ||
				f.getSignatureSource().isHigherPriorityThan(SourceType.ANALYSIS)) {
				return false;
			}
			if (s instanceof Param p) {
				f.getParameter(p.index()).setDataType(pointer, SourceType.ANALYSIS);
			}
			else if (!noReturns.contains(f.getEntryPoint())) {
				f.setReturnType(pointer, SourceType.ANALYSIS);
			}
			else {
				return false;
			}
			return true;
		}
		catch (InvalidInputException | CodeUnitInsertionException e) {
			Msg.warn(E200Analyzer.class, "Could not type " + s + ": " + e.getMessage());
			return false;
		}
	}

	/**
	 * Gives a place that analysis typed as an integer the integer of the other signedness;
	 * returns whether it did
	 */
	private static boolean setInteger(Program program, Slot s, DataType type,
			Set<Address> globals, Set<Function> complete) {
		try {
			if (s instanceof Global g) {
				Data data = program.getListing().getDefinedDataAt(g.address());
				if (!globals.contains(g.address()) || data == null ||
					data.getLength() != type.getLength()) {
					return false;
				}
				program.getListing().clearCodeUnits(g.address(), data.getMaxAddress(), false);
				program.getListing().createData(g.address(), type);
				return true;
			}
			Function f = function(program, s);
			if (f == null || !complete.contains(f) || f.isThunk() ||
				f.getSignatureSource().isHigherPriorityThan(SourceType.ANALYSIS)) {
				return false;
			}
			if (s instanceof Param p) {
				f.getParameter(p.index()).setDataType(type, SourceType.ANALYSIS);
			}
			else {
				f.setReturnType(type, SourceType.ANALYSIS);
			}
			return true;
		}
		catch (InvalidInputException | CodeUnitInsertionException e) {
			Msg.warn(E200Analyzer.class, "Could not type " + s + ": " + e.getMessage());
			return false;
		}
	}

	private static List<DataType> informativeOnly(List<DataType> types) {
		return types.stream().filter(E200TypeFlow::informative).toList();
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
			DataType unsignedTarget;
			if (target instanceof Pointer pTarget) {
				unsignedTarget = defaultType(pTarget, group);
			}
			else {
				unsignedTarget = unsigned(target);
			}
			if (unsignedTarget == null) {
				return null;
			}
			for (DataType t : group) {
				if (t instanceof Pointer p) {
					if (p.getDataType() == null || !fits(p.getDataType(), unsignedTarget)) {
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
		return switch (undefined.getLength()) {
			case 1 -> ByteDataType.dataType;
			case 2 -> UnsignedShortDataType.dataType;
			case 4 -> UnsignedIntegerDataType.dataType;
			case 8 -> UnsignedLongLongDataType.dataType;
			default -> null;
		};
	}

	/**
	 * Whether a place may still get a type: it is of undefined type, or a pointer to
	 * undefined data (a return value of DEFAULT type is not known to exist)
	 */
	static boolean open(Program program, Slot s) {
		DataType current = current(program, s);
		return isOpen(current);
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

	/** The current type of a place, or null if it is not there */
	private static DataType current(Program program, Slot s) {
		if (s instanceof Global g) {
			Data data = program.getListing().getDefinedDataAt(g.address());
			return data == null ? null : data.getDataType();
		}
		Function f = function(program, s);
		if (f == null) {
			return null;
		}
		if (s instanceof Param p) {
			return p.index() < f.getParameterCount() ? f.getParameter(p.index()).getDataType()
					: null;
		}
		return f.getReturnType();
	}

	private static Function function(Program program, Slot s) {
		Address entry = s instanceof Param p ? p.function()
				: s instanceof Return r ? r.function() : null;
		return entry == null ? null : program.getFunctionManager().getFunctionAt(entry);
	}

	/** Gives a place of undefined type the type, if it fits and may change; returns whether */
	private static boolean set(Program program, Slot s, DataType type, Set<Address> globals,
			Set<Function> complete, Set<Address> noReturns) {
		try {
			if (s instanceof Global g) {
				Data data = program.getListing().getDefinedDataAt(g.address());
				return globals.contains(g.address()) && data != null &&
					Undefined.isUndefined(data.getDataType()) &&
					E200DataTypes.applyType(program, g.address(), type);
			}
			Function f = function(program, s);
			if (f == null || !complete.contains(f) || f.isThunk() ||
				f.getSignatureSource().isHigherPriorityThan(SourceType.ANALYSIS)) {
				return false;
			}
			if (s instanceof Param p) {
				if (p.index() >= f.getParameterCount()) {
					return false;
				}
				Parameter param = f.getParameter(p.index());
				if (!fits(param.getDataType(), type)) {
					return false;
				}
				param.setDataType(type, SourceType.ANALYSIS);
				return true;
			}
			if (type instanceof VoidDataType) { // for a return value not known
				if (!(f.getReturnType() instanceof DefaultDataType) &&
					!Undefined.isUndefined(f.getReturnType())) {
					return false;
				}
			}
			else {
				if (f.getReturnType() instanceof DefaultDataType) {
					if (noReturns != null && noReturns.contains(f.getEntryPoint())) {
						return false;
					}
				}
				else if (!fits(f.getReturnType(), type)) {
					return false;
				}
			}
			f.setReturnType(type, SourceType.ANALYSIS);
			return true;
		}
		catch (InvalidInputException e) {
			Msg.warn(E200Analyzer.class, "Could not type " + s + ": " + e.getMessage());
			return false;
		}
	}

	/**
	 * Whether {@code type} can replace {@code current}: an undefined type of its size, or a
	 * pointer to undefined data, by a pointer to data of that size (any size for a pointer to
	 * {@code undefined})
	 */
	static boolean fits(DataType current, DataType type) {
		if (current == null || type == null || type.getLength() != current.getLength()) {
			return false;
		}
		if (Undefined.isUndefined(current)) {
			return !(current instanceof DefaultDataType);
		}
		if (current instanceof Pointer p && type instanceof Pointer q) {
			DataType from = p.getDataType();
			DataType to = q.getDataType();
			if (from == null || to == null) {
				return false;
			}
			if (from instanceof DefaultDataType) {
				return true;
			}
			if (Undefined.isUndefined(from)) {
				return to.getLength() == from.getLength();
			}
			return fits(from, to);
		}
		return false;
	}

	private static Slot find(Map<Slot, Slot> parent, Slot s) {
		Slot root = s;
		for (Slot p = parent.get(root); p != null; p = parent.get(root)) {
			root = p;
		}
		while (!s.equals(root)) { // path compression
			s = parent.put(s, root);
		}
		return root;
	}

	private static void union(Map<Slot, Slot> parent, Slot a, Slot b) {
		Slot ra = find(parent, a);
		Slot rb = find(parent, b);
		if (!ra.equals(rb)) {
			parent.put(ra, rb);
		}
	}
}
