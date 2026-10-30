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
 * <p>
 * A field that holds a pointer gets the type of what code does with the pointer: a pointer
 * to a structure of its own fields, to a single value, to a run of bytes (a buffer), to a
 * function it is called as or that is stored into it, or to the type code casts it to, as
 * when it is passed to a function that knows. A structure built in an earlier round, from
 * the functions decompiled then, gets the field types that later rounds show (see
 * {@link #refine}).
 * <p>
 * The instances of a structure in flash may lie closer together than the fields the code
 * reads reach: integer-valued maps carry a scale and an offset after the descriptor that
 * float maps end with, and the lookup uses them only where the type field says so. The
 * structure is built up to the spacing of its instances, and the fields past it, when the
 * code reads or uses them only under comparisons of a field of the structure with
 * constants, make a structure of their own that follows the instances where the field has
 * such a value (see {@link #extension} and {@link E200Data#structureAt}).
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
		/** The loads of the fields while a function is walked, by offset (see resolveGuards) */
		private final Map<PcodeOp, Long> loads = new IdentityHashMap<>();
		/** The casts of fields' values after arithmetic, to resolve to their guards */
		private final List<Map.Entry<Field, PcodeOp>> pendingCasts = new ArrayList<>();
		/** The indexes the pointer this shape describes is indexed with, while walked */
		private final List<Varnode> indexes = new ArrayList<>();

		boolean isEmpty() {
			return fields.isEmpty() && stride == 0;
		}

		Field field(long offset) {
			return fields.computeIfAbsent(offset, o -> new Field());
		}

		void merge(Shape other) {
			for (Map.Entry<Long, Field> e : other.fields.entrySet()) {
				field(e.getKey()).merge(e.getValue());
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
				int size = e.getValue().size();
				// the fields of the other shape that start in this field
				for (Map.Entry<Long, Field> o : other.fields.subMap(offset, offset + size)
						.entrySet()) {
					int otherSize = o.getValue().size();
					if (o.getKey() == offset ? otherSize != size && otherSize != 1 && size != 1
							: otherSize != 1) {
						return false;
					}
				}
				// the field of the other shape that this field starts in
				Map.Entry<Long, Field> before = other.fields.lowerEntry(offset);
				if (before != null && before.getKey() + before.getValue().size() > offset &&
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
				if (e.getKey() != next || e.getValue().size() != 1) {
					return false;
				}
				next++;
			}
			return true;
		}

		/**
		 * Whether the pointer points to the elements of an array: it is indexed with a
		 * stride, and its fields are the element and the next one, of the stride's size, as
		 * code reads {@code p[i]} and {@code p[i + 1]}. Fields further on are those of a
		 * structure with arrays in it, as {@code p->a[i]} and {@code p->b[i]}.
		 */
		boolean elements() {
			if (mixed || stride == 0 || fields.isEmpty()) {
				return false;
			}
			for (Map.Entry<Long, Field> e : fields.entrySet()) {
				if (e.getKey() != 0 && e.getKey() != stride || e.getValue().size() != stride) {
					return false;
				}
			}
			return true;
		}

		/**
		 * Resolves what the function's p-code says about the fields to the fields: the
		 * comparisons that guard the casts of the fields' values (see {@link E200Code#guard};
		 * where {@code p->f10 == 8} holds on the way to {@code (ushort *)p->fc}, f10 selects
		 * fc's element size, 2 for the value 8), and the fields the indexes of the accesses
		 * through a pointer field derive from ({@code p->x[p->n - 1]}: n counts x's
		 * elements). Called once a function is walked; drops the p-code kept for it.
		 */
		void resolveGuards() {
			for (Map.Entry<PcodeOp, Long> e : loads.entrySet()) {
				// the comparisons of fields of this structure with constants on the way to
				// each load, or to each use of a value loaded before the comparisons, for the
				// fields that follow some instances only (see extension)
				Field f = fields.get(e.getValue());
				if (f == null) {
					continue;
				}
				List<Guard> own = guards(e.getKey());
				if (!own.isEmpty()) {
					f.loadGuards.add(own);
					continue;
				}
				List<PcodeOp> uses = E200Code.consumers(e.getKey().getOutput());
				List<List<Guard>> conjunctions = uses == null || uses.isEmpty() ? null
						: new ArrayList<>();
				for (int i = 0; conjunctions != null && i < uses.size(); i++) {
					List<Guard> conjunction = guards(uses.get(i));
					if (conjunction.isEmpty()) {
						conjunctions = null;
					}
					else {
						conjunctions.add(conjunction);
					}
				}
				if (conjunctions == null) {
					f.unguardedLoads++;
				}
				else {
					f.loadGuards.addAll(conjunctions);
				}
			}
			for (Field f : fields.values()) {
				for (Varnode index : f.target.indexes) {
					for (Map.Entry<PcodeOp, Boolean> e : E200Code.loadsBehind(index, 256)
							.entrySet()) {
						Long offset = loads.get(e.getKey());
						if (offset != null && e.getValue()) {
							f.indexFields.add(offset); // through arithmetic: a bound, not an index
						}
					}
				}
			}
			for (Map.Entry<Field, PcodeOp> e : pendingCasts) {
				Map.Entry<Varnode, Long> guard = E200Code.guard(e.getValue());
				PcodeOp load = guard == null ? null : E200Code.loadOf(guard.getKey());
				Long selector = load == null ? null : loads.get(load);
				DataType t = e.getValue().getOutput().getHigh().getDataType();
				if (selector != null && t instanceof Pointer p && p.getDataType() != null &&
					p.getDataType().getLength() > 0) {
					e.getKey().selectorSizes.computeIfAbsent(selector, k -> new TreeMap<>())
							.putIfAbsent(guard.getValue(), p.getDataType().getLength());
				}
			}
			pendingCasts.clear();
			loads.clear();
			indexes.clear();
			for (Field f : fields.values()) {
				f.target.resolveGuards();
			}
		}

		/** The comparisons of fields of this structure with constants that hold where an op is */
		private List<Guard> guards(PcodeOp op) {
			List<Guard> conjunction = new ArrayList<>();
			for (E200Code.Comparison c : E200Code.guards(op)) {
				PcodeOp load = E200Code.loadOf(c.value());
				Long selector = load == null ? null : loads.get(load);
				if (selector != null) {
					conjunction.add(new Guard(selector, c.constant(), c.equal()));
				}
			}
			return conjunction;
		}

		/** The accesses of all the fields, as those of one element */
		Field element() {
			Field element = new Field();
			for (Field f : fields.values()) {
				element.merge(f);
			}
			return element;
		}

		/**
		 * Whether the pointer points to a structure: fields other than one at offset 0, and
		 * not only bytes from offset 0 on, as code accesses a buffer, and one stride
		 */
		boolean structure() {
			if (mixed || elements()) {
				return false;
			}
			if (fields.size() == 1) {
				return fields.firstKey() != 0 || stride > fields.firstEntry().getValue().size();
			}
			long next = 0;
			for (Map.Entry<Long, Field> e : fields.entrySet()) {
				if (e.getKey() != next || e.getValue().size() != 1) {
					return true;
				}
				next++;
			}
			return false;
		}
	}

	/** A load or store of a field: its size and the type of the value */
	record Access(int size, DataType type) {
	}

	/**
	 * A comparison of the field at {@code selector} with a constant that holds on the way to
	 * a load: the field equals the constant, or differs from it
	 */
	record Guard(long selector, long value, boolean equal) {
	}

	/** A field of a shape: what code does at one offset */
	static final class Field {
		final List<Access> accesses = new ArrayList<>();
		/** What code does with the field's value as a pointer */
		final Shape target = new Shape();
		/** The pointer types that code casts the field's value to, as {@code (float *)p->f4} */
		final List<DataType> casts = new ArrayList<>();
		/**
		 * The pointer types that code casts the field's value to after indexing it, as
		 * {@code *(ushort *)((int)p->f8 + i * 2)}: the element types the code chooses between
		 */
		final List<DataType> elementCasts = new ArrayList<>();
		/**
		 * The element size each value of a selector field of the structure gives, by the
		 * selector's offset: the code casts the field's value to {@code (ushort *)} where
		 * {@code p->f10 == 8} holds
		 */
		final Map<Long, Map<Long, Integer>> selectorSizes = new TreeMap<>();
		/**
		 * The offsets of the fields of the structure that the indexes of the accesses
		 * through this field's value derive from: the count fields of the array it points to
		 */
		final Set<Long> indexFields = new TreeSet<>();
		/** The entry points of functions stored in the field */
		final Set<Address> targets = new TreeSet<>();
		/** The calls through the field's value */
		final List<E200FunctionPointers.Call> calls = new ArrayList<>();
		/**
		 * The comparisons of fields of the structure with constants that hold on the way to
		 * each load of the field, or to each use of a value loaded before them, one list per
		 * load or use (see {@link Shape#resolveGuards})
		 */
		final List<List<Guard>> loadGuards = new ArrayList<>();
		/** The loads of the field that no such comparison guards */
		int unguardedLoads;
		/** The stores to the field */
		int stores;

		/** The size most accesses of the field have, the larger on a tie */
		int size() {
			return E200Types.mostFrequent(accesses.stream().map(Access::size).toList());
		}

		void merge(Field other) {
			accesses.addAll(other.accesses);
			target.merge(other.target);
			casts.addAll(other.casts);
			elementCasts.addAll(other.elementCasts);
			other.selectorSizes.forEach((offset, sizes) -> selectorSizes
					.computeIfAbsent(offset, k -> new TreeMap<>())
					.putAll(sizes));
			indexFields.addAll(other.indexFields);
			targets.addAll(other.targets);
			calls.addAll(other.calls);
			loadGuards.addAll(other.loadGuards);
			unguardedLoads += other.unguardedLoads;
			stores += other.stores;
		}
	}

	// ---- Collection ---------------------------------------------------------------------------

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
				Function callee = E200Code.callee(functions, op);
				if (callee != null) {
					Shape shape = new Shape();
					walk(functions, op.getOutput(), 0, shape, new HashSet<>(), 0);
					shape.resolveGuards();
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
		shape.resolveGuards();
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
						long o = offset + E200Code.signed(other);
						if (o >= 0 && o <= MAX_OFFSET) {
							walk(functions, out, o, shape, seen, depth);
						}
					}
					else if (offset == 0 && op.getOpcode() == PcodeOp.INT_ADD) {
						index(functions, out, other, E200Code.stride(other), shape, seen, depth);
					}
				}
				case PcodeOp.PTRADD -> {
					if (op.getInput(0) != v || !op.getInput(2).isConstant()) {
						break;
					}
					long size = op.getInput(2).getOffset();
					if (op.getInput(1).isConstant()) {
						long o = offset + E200Code.signed(op.getInput(1)) * size;
						if (o >= 0 && o <= MAX_OFFSET) {
							walk(functions, out, o, shape, seen, depth);
						}
					}
					else if (offset == 0) {
						index(functions, out, op.getInput(1),
							size * E200Code.stride(op.getInput(1)), shape, seen, depth);
					}
				}
				case PcodeOp.LOAD -> {
					if (op.getInput(1) == v && out != null) {
						Field f = shape.field(offset);
						shape.loads.put(op, offset);
						DataType type = E200Integers.of(out);
						if (type instanceof Pointer && (out.getSize() == 4 || out.getSize() == 8) &&
							E200Code.usedAsFloat(out)) {
							// a float that the decompiler typed after the field of a
							// structure there, as p[1].f4 for the word after p
							type = out.getSize() == 4 ? FloatDataType.dataType
									: DoubleDataType.dataType;
						}
						f.accesses.add(new Access(out.getSize(), type));
						if (out.getSize() == 4) {
							DataType cast = E200Code.castTo(out);
							if (cast != null) {
								f.casts.add(cast);
							}
							for (PcodeOp elementCast : E200Code.castOpsAfterArithmetic(out)) {
								f.elementCasts.add(
									elementCast.getOutput().getHigh().getDataType());
								shape.pendingCasts.add(Map.entry(f, elementCast));
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
						Varnode value = op.getInput(2);
						Field f = shape.field(offset);
						f.accesses.add(new Access(value.getSize(), E200Integers.of(value)));
						f.stores++;
						Address target = E200Code.addressOf(functions.getProgram(), value, 0);
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

	/**
	 * The pointer indexed with {@code index}, of {@code stride}: an element, whose fields are
	 * the shape's
	 */
	private static void index(FunctionManager functions, Varnode element, Varnode index,
			long stride, Shape shape, Set<Varnode> seen, int depth) {
		shape.indexes.add(index);
		if (stride <= 1 || stride > MAX_OFFSET) {
			return; // bytes, as in a buffer
		}
		shape.mixed |= shape.stride != 0 && shape.stride != stride;
		shape.stride = shape.stride == 0 ? stride : Math.max(shape.stride, stride);
		walk(functions, element, 0, shape, seen, depth);
	}

	// ---- Structures ---------------------------------------------------------------------------

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
		StructureDataType structure =
			new StructureDataType(E200Types.CATEGORY, name, 0, manager);
		long end = 0;
		Map<Long, DataType> types = new TreeMap<>();
		Map<Long, String> comments = new HashMap<>();
		for (Map.Entry<Long, Field> e : shape.fields.entrySet()) {
			long offset = e.getKey();
			Field f = e.getValue();
			int size = f.size();
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
					DataType cast = f.casts.isEmpty() ? null : castType(f.casts);
					if (cast instanceof Pointer p && E200Types.ownStructure(p.getDataType()) &&
						elementsOf((Structure) p.getDataType(), f.target)) {
						// passed on as a pointer to a structure of the analyzer's whose
						// elements the accesses through it are fields of, as p->f14->f8 is
						// the first field of p->f14[1]: what it points to, an array of them
						type = cast;
					}
					else {
						Structure target = build(program, definitions, f.target,
							name + "_f" + Long.toHexString(offset), signedChar, depth + 1, 0,
							new TreeMap<>());
						type = target == null ? null : new PointerDataType(target, 4, manager);
					}
				}
				else if (f.target.elements()) {
					// the elements of an array, read as p[i] and p[i + 1]
					DataType elementType =
						fieldType(f.target.element(), (int) f.target.stride, signedChar);
					type = new PointerDataType(elementType, 4, manager);
				}
				else if (f.target.fields.size() == 1 || f.target.buffer()) {
					// a single value, or bytes from offset 0 on; or a structure of the
					// analyzer's that code casts the pointer to, whose first field the value is
					Field first = f.target.fields.firstEntry().getValue();
					DataType targetType = fieldType(first, first.size(), signedChar);
					DataType cast = f.casts.isEmpty() ? null : castType(f.casts);
					if (cast instanceof Pointer p && E200Types.ownStructure(p.getDataType()) &&
						firstField((Structure) p.getDataType(), f.target.fields.firstKey(),
							first.size())) {
						type = cast;
					}
					else {
						type = targetType == null ? null
								: new PointerDataType(targetType, 4, manager);
					}
				}
			}
			if (type == null && size == 4 && !f.casts.isEmpty()) {
				type = castType(f.casts); // passed on to functions that know what it points to
			}
			if (type == null) {
				type = fieldType(f, size, signedChar);
			}
			if (size == 4 && !f.elementCasts.isEmpty() &&
				(Undefined.isUndefined(type) || E200Types.integer(type))) {
				// the value is indexed and cast to pointer types, as (float *)(p->fc + i * 4):
				// a pointer, to what the casts say or what the code chooses at run time
				DataType cast = castType(f.elementCasts);
				type = cast != null ? cast
						: new PointerDataType(VoidDataType.dataType, 4, manager);
			}
			if (type instanceof Pointer p && !E200Types.informative(p) &&
				(!f.casts.isEmpty() || !f.elementCasts.isEmpty())) {
				// the code chooses what it points to at run time: the types it casts it to,
				// and the selector, for the arrays at the instances (see E200FieldArrays)
				List<DataType> casts = new ArrayList<>(f.casts);
				casts.addAll(f.elementCasts);
				String comment = castsComment(casts);
				String selector = selectorComment(f);
				comments.put(offset, comment == null ? selector : selector == null ? comment
						: comment + "; " + selector);
			}
			types.put(offset, type);
			end = offset + size;
		}
		if (types.isEmpty()) {
			return null;
		}
		// the fields that count the elements of the arrays the pointer fields point to: the
		// integer fields the indexes derive from, now that the fields have their types
		for (Map.Entry<Long, Field> e : shape.fields.entrySet()) {
			String count = countComment(e.getValue(), types);
			if (count != null && types.get(e.getKey()) instanceof Pointer) {
				comments.merge(e.getKey(), count, (a, b) -> a + "; " + b);
			}
		}
		comments.values().removeIf(String::isEmpty);
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
				e.getValue().getLength(), "f" + Long.toHexString(e.getKey()),
				comments.get(e.getKey()));
		}
		return structure;
	}

	/**
	 * The fields past {@code limit}, the spacing of a structure's instances, that code reads
	 * only where a field of the structure has some values: a structure of them, named
	 * {@code <name>_ext}, which follows the instances that have such a value, and the rule
	 * ({@code f10 != 0}, or {@code f2 = 4, 8, c, 10}). The scale and offset of an
	 * integer-valued map follow its descriptor, which a float map ends with, and the lookups
	 * use them only in the branches of the integer types. A field counts when each load of it,
	 * or each use of a value loaded before the comparisons, lies where comparisons of one
	 * integer field below the limit with constants hold (see {@link Shape#resolveGuards}); the
	 * fields keep their names, {@code f14} at offset 0 of the structure that follows. Null
	 * where no field lies past the limit, a field there is written, or read or used without
	 * such a comparison, or the comparisons leave no value out.
	 */
	static Map.Entry<Structure, String> extension(Program program,
			E200FunctionPointers.Definitions definitions, Shape shape, String name,
			boolean signedChar, long limit, TreeMap<Long, DataType> pieces) {
		if (limit <= 0 || shape.fields.ceilingKey(limit) == null) {
			return null;
		}
		List<List<Guard>> conjunctions = new ArrayList<>();
		long end = limit;
		for (Map.Entry<Long, Field> e : shape.fields.tailMap(limit).entrySet()) {
			Field f = e.getValue();
			if (f.size() == 0) {
				continue;
			}
			if (f.unguardedLoads > 0 || f.stores > 0 || f.loadGuards.isEmpty()) {
				return null; // read or used without a comparison, or written
			}
			conjunctions.addAll(f.loadGuards);
			end = Math.max(end, e.getKey() + f.size());
		}
		if (conjunctions.isEmpty()) {
			return null;
		}
		// the selector: a field below the limit that every conjunction compares
		Long selector = null;
		for (Guard g : conjunctions.get(0)) {
			boolean everywhere = g.selector() < limit;
			for (List<Guard> c : conjunctions) {
				everywhere &= c.stream().anyMatch(h -> h.selector() == g.selector());
			}
			if (everywhere) {
				selector = g.selector();
				break;
			}
		}
		Field selected = selector == null ? null : shape.fields.get(selector);
		if (selected == null || selected.size() == 0 || selected.size() > 4) {
			return null;
		}
		Set<Long> present = new TreeSet<>(); // the values whose branches read the fields
		Set<Long> absent = null; // the values no branch without an equality reads them in
		for (List<Guard> conjunction : conjunctions) {
			Set<Long> equal = new TreeSet<>();
			Set<Long> other = new TreeSet<>();
			for (Guard g : conjunction) {
				if (g.selector() == selector) {
					(g.equal() ? equal : other).add(g.value());
				}
			}
			if (equal.size() > 1) {
				continue; // never holds
			}
			if (equal.size() == 1) {
				long value = equal.iterator().next();
				if (!other.contains(value)) {
					present.add(value);
				}
			}
			else if (absent == null) {
				absent = other;
			}
			else {
				absent.retainAll(other);
			}
		}
		String rule;
		if (absent != null) {
			absent.removeAll(present);
			if (absent.isEmpty()) {
				return null; // read whatever the value
			}
			rule = "f" + Long.toHexString(selector) + " != " + values(absent);
		}
		else if (!present.isEmpty()) {
			rule = "f" + Long.toHexString(selector) + " = " + values(present);
		}
		else {
			return null;
		}
		// the pieces past the limit are the data of the next instance, not of this one
		Structure full = build(program, definitions, shape, name + "_ext", signedChar, 0, end,
			new TreeMap<>(pieces.headMap(limit)));
		if (full == null || full.getLength() <= limit) {
			return null;
		}
		StructureDataType tail = new StructureDataType(E200Types.CATEGORY, name + "_ext",
			(int) (full.getLength() - limit), program.getDataTypeManager());
		for (DataTypeComponent c : full.getDefinedComponents()) {
			if (c.getOffset() >= limit) {
				tail.replaceAtOffset((int) (c.getOffset() - limit), c.getDataType(), c.getLength(),
					c.getFieldName(), c.getComment());
			}
		}
		if (tail.getNumDefinedComponents() == 0) {
			return null;
		}
		tail.setDescription("The fields from offset 0x" + Long.toHexString(limit) + " of " +
			name + ", which the code reads where " + rule);
		return Map.entry(tail, rule);
	}

	private static String values(Set<Long> values) {
		List<String> names = new ArrayList<>();
		for (long v : values) {
			names.add(Long.toHexString(v));
		}
		return String.join(", ", names);
	}

	/**
	 * Whether the accesses of a shape are fields of a structure, or of the elements of an
	 * array of it: at the offset of a field modulo the structure's length, of the field's
	 * size, with no type of another kind, and no index with another stride
	 */
	private static boolean elementsOf(Structure s, Shape shape) {
		int length = s.getLength();
		if (length <= 0 || shape.fields.isEmpty() ||
			shape.stride != 0 && shape.stride != length) {
			return false;
		}
		for (Map.Entry<Long, Field> e : shape.fields.entrySet()) {
			Field f = e.getValue();
			int size = f.size();
			if (size == 0) {
				continue;
			}
			int offset = (int) (e.getKey() % length);
			DataTypeComponent c = s.getComponentAt(offset);
			if (c == null || c.getOffset() != offset || c.getLength() != size ||
				c.getDataType() instanceof DefaultDataType) {
				return false;
			}
			for (Access a : f.accesses) {
				if (a.type() != null && E200Types.informative(a.type()) &&
					E200Types.informative(c.getDataType()) &&
					E200Types.kind(a.type()) != E200Types.kind(c.getDataType())) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Whether a value of {@code size} at {@code offset} is the field of a structure there, or
	 * lies in bytes of it that are undefined or a byte of a field
	 */
	private static boolean firstField(Structure s, long offset, int size) {
		if (offset < 0 || offset + size > s.getLength()) {
			return false;
		}
		DataTypeComponent c = s.getComponentContaining((int) offset);
		return c == null || c.getDataType() instanceof DefaultDataType ||
			c.getOffset() == offset && (c.getLength() == size || size == 1);
	}

	/**
	 * {@code f0 * f2 elements}: the integer fields that the indexes of the accesses through
	 * the field's value derive from, one or two of them, which count the elements of the
	 * array it points to (the pointer fields they also derive from, as the search loops take
	 * the difference of two pointers, do not count); null for none or more
	 */
	private static String countComment(Field f, Map<Long, DataType> types) {
		List<String> names = new ArrayList<>();
		for (long offset : f.indexFields) {
			DataType t = types.get(offset);
			if (t != null && t.getLength() <= 4 &&
				(E200Types.integer(t) || Undefined.isUndefined(t))) {
				names.add("f" + Long.toHexString(offset));
			}
		}
		if (names.isEmpty() || names.size() > 2) {
			return null;
		}
		return String.join(" * ", names) + " elements";
	}

	/**
	 * {@code element size by f10: 0=4, 4=1, 8=2}: the selector field the code compares with
	 * the most constants on the way to the casts, and the element size each gives (see
	 * E200FieldArrays); null if no field is compared with two
	 */
	private static String selectorComment(Field f) {
		Map.Entry<Long, Map<Long, Integer>> best = null;
		for (Map.Entry<Long, Map<Long, Integer>> e : f.selectorSizes.entrySet()) {
			if (e.getValue().size() >= 2 &&
				(best == null || e.getValue().size() > best.getValue().size())) {
				best = e;
			}
		}
		if (best == null) {
			return null;
		}
		StringBuilder sb = new StringBuilder("element size by f")
				.append(Long.toHexString(best.getKey()))
				.append(':');
		String separator = " ";
		for (Map.Entry<Long, Integer> e : best.getValue().entrySet()) {
			sb.append(separator).append(Long.toHexString(e.getKey())).append('=').append(e.getValue());
			separator = ", ";
		}
		return sb.toString();
	}

	/** {@code cast to /float, /ushort}: the distinct types the casts point to, by path */
	private static String castsComment(List<DataType> casts) {
		Set<String> names = new TreeSet<>();
		for (DataType t : casts) {
			if (t instanceof Pointer p && p.getDataType() != null &&
				p.getDataType().getLength() > 0) {
				names.add(p.getDataType().getPathName());
			}
		}
		return names.isEmpty() ? null : "cast to " + String.join(", ", names);
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
			if (E200Types.ownStructurePointer(t)) {
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
	 * The type of a field: the one its accesses of {@code size} agree on, else undefined. A
	 * pointer type counts only when every access has it, as when the loaded value is passed
	 * to a function whose parameter says what it points to.
	 */
	private static DataType fieldType(Field f, int size, boolean signedChar) {
		List<DataType> types = new ArrayList<>();
		boolean pointers = true;
		for (Access a : f.accesses) {
			DataType t = a.type();
			if (a.size() == size && t != null && E200Types.informative(t) &&
				t.getLength() == size) {
				types.add(t);
				pointers &= t instanceof Pointer;
			}
			else {
				pointers = false;
			}
		}
		if (!pointers) {
			types.removeIf(t -> t instanceof Pointer);
		}
		DataType type = types.isEmpty() ? null : E200Types.chooseType(types, signedChar, true);
		return type != null && type.getLength() == size ? type
				: Undefined.getUndefinedDataType(size);
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
			if (type instanceof Pointer p && E200Types.ownStructure(p.getDataType())) {
				Structure nested = (Structure) p.getDataType();
				DataType known = manager.getDataType(E200Types.CATEGORY, nested.getName());
				if (known instanceof Structure s && s != nested) {
					refine(manager, s, nested);
					type = new PointerDataType(s, 4, manager);
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
				if (!free || !E200Types.informative(type)) {
					continue;
				}
			}
			else if (current.getOffset() != offset || current.getLength() != length ||
				!refinable(current.getDataType(), type)) {
				// the type stays; what the round shows about the field's arrays may be new
				if (current.getOffset() == offset && current.getLength() == length &&
					c.getComment() != null && !c.getComment().equals(current.getComment())) {
					existing.replaceAtOffset(offset, current.getDataType(), length,
						current.getFieldName(), mergedComment(c.getComment(), current.getComment()));
					changed++;
				}
				continue;
			}
			String comment = c.getComment() != null ? c.getComment()
					: current == null ? null : current.getComment();
			existing.replaceAtOffset(offset, type, length, c.getFieldName(), comment);
			changed++;
		}
		return changed;
	}

	/**
	 * The comment a round built for a field, with the parts of the field's comment so far
	 * that it lacks (the count the instances voted, the selector): the code of a later round
	 * says more, the instances still what they said
	 */
	private static String mergedComment(String built, String existing) {
		if (existing == null) {
			return built;
		}
		List<String> parts = new ArrayList<>(List.of(built.split("; ")));
		for (String part : existing.split("; ")) {
			boolean count = part.endsWith(" elements");
			boolean selector = part.startsWith("element size by");
			boolean has = parts.stream().anyMatch(
				q -> count && q.endsWith(" elements") || selector && q.startsWith("element size by"));
			if ((count || selector) && !has) {
				parts.add(part);
			}
		}
		return String.join("; ", parts);
	}

	/**
	 * Whether {@code type} says more about a field than its {@code current} type: the field was
	 * undefined or an integer and is a pointer or a float now, or was undefined and has a type
	 * now, or pointed to undefined and points to something now, or pointed to a single value
	 * and points to a structure of the analyzer's whose first field that value is now (an
	 * early round sees the value read, a later one the pointer cast to the structure)
	 */
	private static boolean refinable(DataType current, DataType type) {
		if (!E200Types.informative(type) || type.isEquivalent(current)) {
			return false;
		}
		if (Undefined.isUndefined(current)) {
			return true;
		}
		if (current instanceof AbstractIntegerDataType) {
			return type instanceof Pointer || type instanceof AbstractFloatDataType;
		}
		if (current instanceof Pointer p && type instanceof Pointer q) {
			if (!E200Types.informative(p)) {
				return true;
			}
			if (E200Types.ownStructure(p.getDataType()) &&
				E200Types.ownStructure(q.getDataType()) &&
				untypedFieldsOf((Structure) p.getDataType(), (Structure) q.getDataType())) {
				// a structure of untyped words that are fields of the structure, or of the
				// elements of an array of it, that code passes the pointer on as
				return true;
			}
			return E200Types.ownStructure(q.getDataType()) && replaceable(current) &&
				firstField((Structure) q.getDataType(), 0, p.getDataType().getLength());
		}
		return false;
	}

	/**
	 * Whether the fields of a structure are all undefined and each lies where a field of
	 * {@code other} of its size does, or that field of an element of an array of it
	 */
	private static boolean untypedFieldsOf(Structure structure, Structure other) {
		int length = other.getLength();
		if (length <= 0 || structure.getNumDefinedComponents() == 0 ||
			structure.isEquivalent(other)) {
			return false;
		}
		for (DataTypeComponent c : structure.getDefinedComponents()) {
			if (!Undefined.isUndefined(c.getDataType())) {
				return false;
			}
			int offset = c.getOffset() % length;
			DataTypeComponent o = other.getComponentAt(offset);
			if (o == null || o.getOffset() != offset || o.getLength() != c.getLength() ||
				o.getDataType() instanceof DefaultDataType) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Whether a place's type may become a pointer to a structure: an integer or undefined
	 * value of a pointer's size, or a pointer to a single value, not set by the user
	 */
	static boolean replaceable(DataType current) {
		if (current == null || current.getLength() != 4 || current instanceof DefaultDataType ||
			current instanceof TypeDef) {
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
