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

import ghidra.app.plugin.core.analysis.E200TypeFlow.*;
import ghidra.program.model.address.Address;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.*;

/**
 * Structures that pointers point to (part of {@link E200TypeFlow}).
 * <p>
 * A function that reads or writes through a pointer at constant offsets, as in
 * {@code *(int *)(param_1 + 8)} and {@code *(byte *)(param_1 + 0x15)}, uses a structure the
 * decompiler does not know. The shape of a pointer value is what code does with it: the
 * fields it loads and stores at each offset, with their sizes and types, and for a field
 * that is itself a pointer the shape of what it points to. Indexing it with a stride, as in
 * {@code param_1 + i * 0x14}, makes it a pointer to elements of that size; indexing it with
 * several, as a lookup table whose element type a field selects, makes it a {@code void *}.
 * <p>
 * The shapes of the values of linked places (parameters, return values and globals that the
 * same values pass through, see {@link E200TypeFlow}) are merged. A group whose shape has a
 * field at an offset other than 0, or several fields that are not all the bytes from offset
 * 0 on (which code accesses in buffers), gets a structure of these fields named
 * after one of its places ({@code P_<global>}, {@code P_<function>_<parameter>} or
 * {@code P_<function>_ret}), fields {@code f<offset>}, and its places that hold an integer or
 * a pointer to a single value, as the decompiler typed them, get a pointer to it. A field of
 * a size that differs from that of most accesses at its offset, or that overlaps the
 * previous field, is left out. Places of another type, such as a pointer to a structure
 * already, are left alone, and so is a group with a place that gets a constant that is no
 * address in memory, as an error code passed where other callers pass a pointer.
 */
final class E200Structures {

	/** Levels of pointers followed from a place */
	private static final int MAX_DEPTH = 3;
	/** Largest field offset */
	private static final long MAX_OFFSET = 0x1000;
	/** Varnodes followed from a place */
	private static final int MAX_VARNODES = 4000;

	private E200Structures() {
	}

	/**
	 * What code does with a pointer: fields at constant offsets, a stride if indexed, and
	 * whether it is indexed with several strides, as data whose type is chosen at run time
	 */
	static final class Shape {
		final TreeMap<Long, Field> fields = new TreeMap<>();
		long stride;
		boolean mixed;

		boolean isEmpty() {
			return fields.isEmpty() && stride == 0;
		}

		Field field(long offset) {
			return fields.computeIfAbsent(offset, o -> new Field());
		}

		void merge(Shape other) {
			for (Map.Entry<Long, Field> e : other.fields.entrySet()) {
				Field f = field(e.getKey());
				f.sizes.addAll(e.getValue().sizes);
				f.types.addAll(e.getValue().types);
				f.target.merge(e.getValue().target);
				f.casts.addAll(e.getValue().casts);
				f.targets.addAll(e.getValue().targets);
				f.calls.addAll(e.getValue().calls);
			}
			mixed |= other.mixed || stride != 0 && other.stride != 0 && stride != other.stride;
			stride = Math.max(stride, other.stride);
		}

		/**
		 * Whether two shapes describe data of one layout, as the shapes of pointers to the
		 * same global do: neither is indexed with several strides, their strides agree, and
		 * where their fields overlap they are the same field, of one size, or bytes of a field
		 * of the other (code reads a word and its bytes)
		 */
		boolean compatible(Shape other) {
			if (mixed || other.mixed || stride != 0 && other.stride != 0 && stride != other.stride) {
				return false;
			}
			for (Map.Entry<Long, Field> e : fields.entrySet()) {
				long offset = e.getKey();
				int size = size(e.getValue());
				// the fields of the other shape that start in this field
				for (Map.Entry<Long, Field> o : other.fields.subMap(offset, offset + size)
						.entrySet()) {
					int otherSize = size(o.getValue());
					if (o.getKey() == offset ? otherSize != size && otherSize != 1 && size != 1
							: otherSize != 1) {
						return false;
					}
				}
				// the field of the other shape that this field starts in
				Map.Entry<Long, Field> before = other.fields.lowerEntry(offset);
				if (before != null && before.getKey() + size(before.getValue()) > offset &&
					size != 1) {
					return false;
				}
			}
			return true;
		}

		/**
		 * Whether the pointer points to a buffer: two or more bytes from offset 0 on, and
		 * nothing else
		 */
		boolean buffer() {
			if (mixed || fields.size() < 2) {
				return false;
			}
			long next = 0;
			for (Map.Entry<Long, Field> e : fields.entrySet()) {
				if (e.getKey() != next || size(e.getValue()) != 1) {
					return false;
				}
				next++;
			}
			return true;
		}

		/**
		 * Whether the pointer points to a structure: fields other than one at offset 0, and
		 * not only bytes from offset 0 on, as code accesses a buffer, and one stride
		 */
		boolean structure() {
			if (mixed) {
				return false;
			}
			if (fields.size() == 1) {
				return fields.firstKey() != 0 || stride > size(fields.firstEntry().getValue());
			}
			long next = 0;
			for (Map.Entry<Long, Field> e : fields.entrySet()) {
				if (e.getKey() != next || size(e.getValue()) != 1) {
					return true;
				}
				next++;
			}
			return false;
		}
	}

	static final class Field {
		final List<Integer> sizes = new ArrayList<>();
		final List<DataType> types = new ArrayList<>();
		final Shape target = new Shape();
		/** The pointer types that code casts the field's value to, as {@code (float *)p->f4} */
		final List<DataType> casts = new ArrayList<>();
		/** The entry points of functions stored in the field */
		final Set<Address> targets = new TreeSet<>();
		/** The calls through the field's value */
		final List<E200FunctionPointers.Call> calls = new ArrayList<>();
	}

	/** The size most accesses of a field have, the larger on a tie */
	private static int size(Field f) {
		return E200DataTypes.mostFrequent(f.sizes);
	}

	/** Adds the shapes of the parameters, globals and call results of a function to facts. */
	static void collect(HighFunction high, Facts facts) {
		Function function = high.getFunction();
		FunctionManager functions = function.getProgram().getFunctionManager();
		Address entry = function.getEntryPoint();
		LocalSymbolMap locals = high.getLocalSymbolMap();
		for (int i = 0; i < locals.getNumParams(); i++) {
			HighSymbol param = locals.getParamSymbol(i);
			add(facts, functions, new Param(entry, param.getCategoryIndex()),
				param.getHighVariable());
		}
		Iterator<HighSymbol> globals = high.getGlobalSymbolMap().getSymbols();
		while (globals.hasNext()) {
			HighSymbol symbol = globals.next();
			HighVariable variable = symbol.getHighVariable();
			if (variable != null && symbol.getStorage() != null &&
				symbol.getStorage().isMemoryStorage() && symbol.getSize() == 4) {
				add(facts, functions, new Global(symbol.getStorage().getMinAddress()), variable);
			}
		}
		Iterator<PcodeOpAST> ops = high.getPcodeOps();
		while (ops.hasNext()) {
			PcodeOpAST op = ops.next();
			if (op.getOpcode() == PcodeOp.CALL && op.getOutput() != null &&
				op.getOutput().getSize() == 4) {
				Function callee = E200TypeFlow.callee(functions, op);
				if (callee != null) {
					Shape shape = new Shape();
					walk(functions, op.getOutput(), 0, shape, new HashSet<>(), 0);
					if (!shape.isEmpty()) {
						facts.shapes.add(Map.entry(new Return(callee.getEntryPoint()), shape));
					}
				}
			}
		}
	}

	private static void add(Facts facts, FunctionManager functions, Slot slot,
			HighVariable variable) {
		if (variable == null || variable.getSize() != 4) {
			return;
		}
		Shape shape = new Shape();
		Set<Varnode> seen = new HashSet<>();
		for (Varnode instance : variable.getInstances()) {
			walk(functions, instance, 0, shape, seen, 0);
		}
		if (!shape.isEmpty()) {
			facts.shapes.add(Map.entry(slot, shape));
		}
	}

	/** Follows a pointer to {@code offset} in the structure {@code shape} describes. */
	private static void walk(FunctionManager functions, Varnode v, long offset, Shape shape,
			Set<Varnode> seen, int depth) {
		if (v == null || !seen.add(v) || seen.size() > MAX_VARNODES) {
			return;
		}
		Iterator<PcodeOp> uses = v.getDescendants();
		while (uses.hasNext()) {
			PcodeOp op = uses.next();
			Varnode out = op.getOutput();
			switch (op.getOpcode()) {
				case PcodeOp.COPY, PcodeOp.CAST, PcodeOp.MULTIEQUAL, PcodeOp.INDIRECT ->
					walk(functions, out, offset, shape, seen, depth);
				case PcodeOp.INT_ADD, PcodeOp.PTRSUB -> {
					Varnode other = op.getInput(0) == v ? op.getInput(1) : op.getInput(0);
					if (other.isConstant()) {
						long o = offset + signed(other);
						if (o >= 0 && o <= MAX_OFFSET) {
							walk(functions, out, o, shape, seen, depth);
						}
					}
					else if (offset == 0 && op.getOpcode() == PcodeOp.INT_ADD) {
						index(functions, out, stride(other), shape, seen, depth);
					}
				}
				case PcodeOp.PTRADD -> {
					if (op.getInput(0) != v || !op.getInput(2).isConstant()) {
						break;
					}
					long size = op.getInput(2).getOffset();
					if (op.getInput(1).isConstant()) {
						long o = offset + signed(op.getInput(1)) * size;
						if (o >= 0 && o <= MAX_OFFSET) {
							walk(functions, out, o, shape, seen, depth);
						}
					}
					else if (offset == 0) {
						index(functions, out, size * stride(op.getInput(1)), shape, seen, depth);
					}
				}
				case PcodeOp.LOAD -> {
					if (op.getInput(1) == v && out != null) {
						Field f = shape.field(offset);
						f.sizes.add(out.getSize());
						f.types.add(type(out));
						if (out.getSize() == 4) {
							DataType cast = E200Tables.castTo(out);
							if (cast != null) {
								f.casts.add(cast);
							}
							calls(out, f.calls, 0);
							if (depth < MAX_DEPTH) {
								walk(functions, out, 0, f.target, new HashSet<>(), depth + 1);
							}
						}
					}
				}
				case PcodeOp.STORE -> {
					if (op.getInput(1) == v) {
						Field f = shape.field(offset);
						f.sizes.add(op.getInput(2).getSize());
						f.types.add(type(op.getInput(2)));
						Address target = E200TypeFlow.addressOf(functions.getProgram(),
							op.getInput(2), 0);
						if (target != null && functions.getFunctionAt(target) != null) {
							f.targets.add(target);
						}
					}
				}
				default -> {
					// not a use as a pointer
				}
			}
		}
	}

	/**
	 * Adds the calls through a loaded value, as {@code (*p->f8)(x)}; the decompiler casts the
	 * value first.
	 */
	private static void calls(Varnode value, List<E200FunctionPointers.Call> calls,
			int depth) {
		if (value == null || depth > 3) {
			return;
		}
		Iterator<PcodeOp> uses = value.getDescendants();
		while (uses.hasNext()) {
			PcodeOp op = uses.next();
			if (op.getOpcode() == PcodeOp.CALLIND && op.getInput(0) == value) {
				calls.add(E200FunctionPointers.Call.of(op));
			}
			else if (op.getOpcode() == PcodeOp.CAST || op.getOpcode() == PcodeOp.COPY) {
				calls(op.getOutput(), calls, depth + 1);
			}
		}
	}

	/** The pointer indexed with {@code stride}: an element, whose fields are the shape's */
	private static void index(FunctionManager functions, Varnode element, long stride,
			Shape shape, Set<Varnode> seen, int depth) {
		if (stride <= 1 || stride > MAX_OFFSET) {
			return; // bytes, as in a buffer
		}
		shape.mixed |= shape.stride != 0 && shape.stride != stride;
		shape.stride = shape.stride == 0 ? stride : Math.max(shape.stride, stride);
		walk(functions, element, 0, shape, seen, depth);
	}

	/** The multiplier of an index, as in {@code i * 0x14} or {@code i << 2}, else 1 */
	private static long stride(Varnode index) {
		PcodeOp def = index.getDef();
		if (def == null) {
			return 1;
		}
		return switch (def.getOpcode()) {
			case PcodeOp.INT_MULT -> def.getInput(1).isConstant() ? def.getInput(1).getOffset()
					: def.getInput(0).isConstant() ? def.getInput(0).getOffset() : 1;
			case PcodeOp.INT_LEFT -> def.getInput(1).isConstant() &&
				def.getInput(1).getOffset() < 16 ? 1L << def.getInput(1).getOffset() : 1;
			case PcodeOp.CAST, PcodeOp.COPY, PcodeOp.INT_ZEXT, PcodeOp.INT_SEXT ->
				stride(def.getInput(0));
			default -> 1;
		};
	}

	private static long signed(Varnode constant) {
		long value = constant.getOffset();
		int bits = constant.getSize() * 8;
		return bits >= 64 ? value : value << (64 - bits) >> (64 - bits);
	}

	private static DataType type(Varnode v) {
		return E200Integers.of(v);
	}

	/**
	 * Builds the structure a shape describes, named {@code name}, with the structures its
	 * pointer fields point to and the function definitions the fields that hold function
	 * pointers point to ({@code definitions}); null if the shape has no fields that fit
	 * together. The structure is at most {@code limit} bytes long if the limit is not 0: the
	 * fields past it, which code reads from a longer variant of the structure, are left out.
	 * The fields that the data at its instances shows to be in pieces are split into them
	 * ({@code pieces}, by offset): code that writes a {@code ushort} where other code reads a
	 * {@code byte} writes two fields at once.
	 */
	static Structure build(Program program, E200FunctionPointers.Definitions definitions,
			Shape shape, String name, boolean signedChar, int depth, long limit,
			TreeMap<Long, DataType> pieces) {
		DataTypeManager manager = program.getDataTypeManager();
		StructureDataType structure = new StructureDataType(E200Tables.CATEGORY, name, 0, manager);
		long end = 0;
		Map<Long, DataType> types = new TreeMap<>();
		for (Map.Entry<Long, Field> e : shape.fields.entrySet()) {
			long offset = e.getKey();
			Field f = e.getValue();
			int size = size(f);
			if (size == 0 || offset < end || limit > 0 && offset + size > limit) {
				continue; // overlaps the previous field, or lies past the limit
			}
			Map<Long, DataType> within = pieces.subMap(offset, offset + size);
			if (!within.isEmpty()) {
				for (Map.Entry<Long, DataType> piece : within.entrySet()) {
					if (piece.getKey() >= end &&
						piece.getKey() + piece.getValue().getLength() <= offset + size) {
						types.put(piece.getKey(), piece.getValue());
						end = piece.getKey() + piece.getValue().getLength();
					}
				}
				end = Math.max(end, offset + size);
				continue;
			}
			DataType type = null;
			if (size == 4 && (!f.targets.isEmpty() || !f.calls.isEmpty())) {
				// a pointer to a function: stored or called through
				FunctionDefinition definition = definitions.of(f.targets, f.calls);
				if (definition != null) {
					type = new PointerDataType(definition, 4, manager);
				}
			}
			if (type == null && size == 4 && !f.target.isEmpty() && depth < MAX_DEPTH) {
				if (f.target.mixed) {
					// elements of a type chosen at run time
					type = new PointerDataType(VoidDataType.dataType, 4, manager);
				}
				else if (f.target.structure()) {
					Structure target = build(program, definitions, f.target,
						name + "_f" + Long.toHexString(offset), signedChar, depth + 1, 0,
						new TreeMap<>());
					type = target == null ? null : new PointerDataType(target, 4, manager);
				}
				else if (f.target.fields.size() == 1 || f.target.buffer()) {
					// a single value, or bytes from offset 0 on
					int targetSize = size(f.target.fields.firstEntry().getValue());
					DataType targetType = fieldType(f.target.fields.firstEntry().getValue(),
						targetSize, signedChar);
					type = targetType == null ? null
							: new PointerDataType(targetType, 4, manager);
				}
			}
			if (type == null && size == 4 && !f.casts.isEmpty()) {
				type = castType(f.casts); // passed on to functions that know what it points to
			}
			if (type == null) {
				type = fieldType(f, size, signedChar);
			}
			types.put(offset, type);
			end = offset + size;
		}
		if (types.isEmpty()) {
			return null;
		}
		// padded to the alignment of its widest field
		long align = 1;
		for (DataType t : types.values()) {
			align = Math.max(align, Math.min(4, t.getLength()));
		}
		long length = (end + align - 1) & -align;
		if (shape.stride >= end) {
			length = shape.stride;
		}
		if (limit > 0 && length > limit) {
			length = Math.max(end, limit);
		}
		structure.growStructure((int) length);
		for (Map.Entry<Long, DataType> e : types.entrySet()) {
			structure.replaceAtOffset(e.getKey().intValue(), e.getValue(),
				e.getValue().getLength(), "f" + Long.toHexString(e.getKey()), null);
		}
		return structure;
	}

	/**
	 * The pointer type that code casts a field's value to, as {@code (float *)p->f4} or a
	 * call's {@code (S *)} parameter: the one the casts agree on, a pointer to a structure of
	 * the analyzer's before one to what it starts with; null if they disagree
	 */
	private static DataType castType(List<DataType> casts) {
		DataType structure = null;
		DataType other = null;
		for (DataType t : casts) {
			if (E200Tables.ownStructurePointer(t)) {
				if (structure != null && !structure.isEquivalent(t)) {
					return null;
				}
				structure = t;
			}
			else if (other != null && !other.isEquivalent(t)) {
				return null;
			}
			else {
				other = t;
			}
		}
		return structure != null ? structure : other;
	}

	/**
	 * Gives the fields of a structure built before the types that a structure built now
	 * from more of the code shows: a field that was undefined or an integer and is a pointer
	 * now, or that was undefined and has a type now, or a new field in bytes that were
	 * undefined; returns how many fields changed. The structures that pointer fields point to
	 * are refined in turn where they exist.
	 */
	static int refine(DataTypeManager manager, Structure existing, Structure built) {
		int changed = 0;
		for (DataTypeComponent c : built.getDefinedComponents()) {
			DataType type = c.getDataType();
			if (type instanceof Pointer p && p.getDataType() instanceof Structure nested &&
				nested.getCategoryPath().equals(E200Tables.CATEGORY)) {
				DataType known = manager.getDataType(E200Tables.CATEGORY, nested.getName());
				if (known instanceof Structure s) {
					if (s != nested) {
						refine(manager, s, nested);
						type = new PointerDataType(s, 4, manager);
					}
				}
			}
			int offset = c.getOffset();
			int length = c.getLength();
			if (offset + length > existing.getLength()) {
				continue;
			}
			DataTypeComponent current = existing.getComponentContaining(offset);
			if (current != null && current.getDataType() instanceof DefaultDataType) {
				current = null; // undefined bytes
			}
			if (current == null) {
				// new bytes: free up to the end of the field
				boolean free = true;
				for (DataTypeComponent o : existing.getDefinedComponents()) {
					if (o.getOffset() < offset + length && o.getOffset() + o.getLength() > offset) {
						free = false;
					}
				}
				if (!free || !E200TypeFlow.informative(type)) {
					continue;
				}
			}
			else if (current.getOffset() != offset || current.getLength() != length ||
				!refinable(current.getDataType(), type)) {
				continue;
			}
			existing.replaceAtOffset(offset, type, length, c.getFieldName(), null);
			changed++;
		}
		return changed;
	}

	/**
	 * Whether {@code type} says more about a field than its {@code current} type: the field was
	 * undefined or an integer and is a pointer or a float now, or was undefined and has a type
	 * now, or pointed to undefined and points to something now
	 */
	private static boolean refinable(DataType current, DataType type) {
		if (!E200TypeFlow.informative(type) || type.isEquivalent(current)) {
			return false;
		}
		if (Undefined.isUndefined(current)) {
			return true;
		}
		if (current instanceof AbstractIntegerDataType) {
			return type instanceof Pointer || type instanceof AbstractFloatDataType;
		}
		if (current instanceof Pointer p && type instanceof Pointer) {
			return !E200TypeFlow.informative(p);
		}
		return false;
	}

	/** The type of a field: the one its accesses of {@code size} agree on, else undefined */
	private static DataType fieldType(Field f, int size, boolean signedChar) {
		List<DataType> types = new ArrayList<>();
		for (int i = 0; i < f.types.size(); i++) {
			DataType t = f.types.get(i);
			if (f.sizes.get(i) == size && t != null && E200TypeFlow.informative(t) &&
				t.getLength() == size && !(t instanceof Pointer)) {
				types.add(t);
			}
		}
		DataType type = types.isEmpty() ? null : E200DataTypes.chooseType(types, signedChar, true);
		return type != null && type.getLength() == size ? type
				: Undefined.getUndefinedDataType(size);
	}

	/**
	 * Whether a place's type may become a pointer to a structure: an integer or undefined
	 * value of a pointer's size, or a pointer to a single value, not set by the user
	 */
	static boolean replaceable(DataType current) {
		if (current == null || current.getLength() != 4 || current instanceof DefaultDataType) {
			return false;
		}
		if (current instanceof TypeDef) {
			return false;
		}
		if (Undefined.isUndefined(current) || current instanceof AbstractIntegerDataType) {
			return true;
		}
		if (current instanceof Pointer p) {
			DataType target = p.getDataType();
			return target == null || target instanceof DefaultDataType ||
				Undefined.isUndefined(target) || target instanceof AbstractIntegerDataType ||
				target instanceof AbstractFloatDataType;
		}
		return false;
	}
}
