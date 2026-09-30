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
		LocalSymbolMap locals = high.getLocalSymbolMap();
		for (int i = 0; i < locals.getNumParams(); i++) {
			HighSymbol param = locals.getParamSymbol(i);
			HighVariable variable = param.getHighVariable();
			if (variable != null) {
				facts.type(new Param(entry, param.getCategoryIndex()), variable.getDataType());
			}
		}
		Iterator<HighSymbol> globals = high.getGlobalSymbolMap().getSymbols();
		while (globals.hasNext()) {
			HighVariable variable = globals.next().getHighVariable();
			Slot global = variable == null ? null : global(variable.getRepresentative());
			if (global != null) {
				facts.type(global, variable.getDataType());
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
		return facts;
	}

	/** A value goes to {@code sink}: its type is one of the sink's, and it links its source. */
	private static void flow(Facts facts, FunctionManager functions, Address entry, Varnode value,
			Slot sink) {
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
	private static Function callee(FunctionManager functions, PcodeOp call) {
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
		if (v == null || v.isConstant() || v.getHigh() == null ||
			v.getHigh() instanceof HighConstant) {
			return null;
		}
		return v.getHigh().getDataType();
	}

	/** Whether the type says more than its size */
	static boolean informative(DataType type) {
		if (type == null || Undefined.isUndefined(type) || type instanceof VoidDataType) {
			return false;
		}
		if (type instanceof Pointer pointer) {
			DataType target = pointer.getDataType();
			return target != null && !Undefined.isUndefined(target) &&
				!(target instanceof VoidDataType);
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
		for (Facts f : facts) {
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
		Map<Slot, List<DataType>> groups = new HashMap<>();
		for (Slot s : slots) {
			groups.computeIfAbsent(find(parent, s), r -> new ArrayList<>())
					.addAll(seen.getOrDefault(s, List.of()));
		}
		boolean signedChar = program.getDataTypeManager().getDataOrganization().isSignedChar();
		Typed typed = new Typed(new ArrayList<>(), new ArrayList<>(), new ArrayList<>());
		for (Slot s : slots) {
			monitor.checkCancelled();
			List<DataType> group = groups.get(find(parent, s));
			DataType type = E200DataTypes.chooseType(
				informativeOnly(seen.getOrDefault(s, List.of())), signedChar, false);
			if (type == null) {
				type = E200DataTypes.chooseType(informativeOnly(group), signedChar, false);
			}
			List<Slot> list = typed.fromValues();
			if (type == null) {
				if (!defaults || group.stream().anyMatch(E200TypeFlow::informative)) {
					continue;
				}
				type = defaultType(current(program, s), group);
				list = typed.byDefault();
			}
			if (type != null && set(program, s, type, globals, complete)) {
				list.add(s);
			}
		}
		if (defaults) {
			// Decompiler Parameter ID leaves the return type of a function that returns
			// nothing undefined, since it does not know whether a caller uses a result
			for (Facts f : facts) {
				Slot r = f.returnsNothing == null ? null : new Return(f.returnsNothing);
				if (r != null && !seen.containsKey(r) && !parent.containsKey(r) &&
					set(program, r, VoidDataType.dataType, globals, complete)) {
					typed.voids().add(r);
				}
			}
		}
		return typed;
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
			DataType unsigned = target == null ? null : unsigned(target);
			if (unsigned == null) {
				return null;
			}
			for (DataType t : group) {
				if (!(t instanceof Pointer p) || p.getDataType() == null ||
					!Undefined.isUndefined(p.getDataType()) ||
					p.getDataType().getLength() != target.getLength()) {
					return null; // a value in the group is not a pointer to data of that size
				}
			}
			return new PointerDataType(unsigned, pointer.getLength());
		}
		DataType unsigned = unsigned(current);
		for (DataType t : group) {
			if (!Undefined.isUndefined(t) || t.getLength() != current.getLength()) {
				return null; // a pointer, or of another size
			}
		}
		return unsigned;
	}

	/** The unsigned integer of the size of undefined data of 1, 2 or 4 bytes, or null */
	private static DataType unsigned(DataType undefined) {
		if (!Undefined.isUndefined(undefined) || undefined instanceof DefaultDataType) {
			return null;
		}
		return switch (undefined.getLength()) {
			case 1 -> ByteDataType.dataType;
			case 2 -> UnsignedShortDataType.dataType;
			case 4 -> UnsignedIntegerDataType.dataType;
			default -> null;
		};
	}

	/**
	 * Whether a place may still get a type: it is of undefined type, or a pointer to
	 * undefined data (a return value of DEFAULT type is not known to exist)
	 */
	static boolean open(Program program, Slot s) {
		DataType current = current(program, s);
		if (current == null || current instanceof DefaultDataType) {
			return false;
		}
		return Undefined.isUndefined(current) || current instanceof Pointer p &&
			p.getDataType() != null && Undefined.isUndefined(p.getDataType());
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
			Set<Function> complete) {
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
				if (!(f.getReturnType() instanceof DefaultDataType)) {
					return false;
				}
			}
			// DEFAULT: no known return value
			else if (f.getReturnType() instanceof DefaultDataType ||
				!fits(f.getReturnType(), type)) {
				return false;
			}
			f.setReturnType(type, SourceType.ANALYSIS);
			return true;
		}
		catch (InvalidInputException e) {
			Msg.warn(E200TypeFlow.class, "Could not type " + s + ": " + e.getMessage());
			return false;
		}
	}

	/**
	 * Whether {@code type} can replace {@code current}: an undefined type of its size, or a
	 * pointer to undefined data, by a pointer to data of that size (any size for a pointer to
	 * {@code undefined})
	 */
	static boolean fits(DataType current, DataType type) {
		if (current == null || type.getLength() != current.getLength()) {
			return false;
		}
		if (Undefined.isUndefined(current)) {
			return !(current instanceof DefaultDataType);
		}
		if (current instanceof Pointer p && type instanceof Pointer q) {
			DataType from = p.getDataType();
			DataType to = q.getDataType();
			if (from == null || !Undefined.isUndefined(from) || to == null) {
				return false;
			}
			return from instanceof DefaultDataType || to.getLength() == from.getLength();
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
