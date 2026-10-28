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

import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.InvalidNameException;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Arrays, and arrays of structures, that code indexes (part of {@link E200DataTypes}).
 * <p>
 * Code reads an element of a global array at the array's address plus the index times the
 * element size, and a field of an element of an array of structures at the address of the
 * field in the first element plus the index times the structure size. Without data of the
 * array's type, the decompiler shows {@code (&UINT_08f9e258)[i * 2]} and
 * {@code (&BYTE_08f9e25c)[i * 8]} for the fields at 0 and 4 of an array of 8-byte
 * structures, and the listing has data for the first element at most.
 * <p>
 * The loads and stores at a constant address plus an index times a stride make tables: those
 * with the same stride whose addresses lie within one stride of the lowest one are the fields
 * of one element, which starts at the lowest. A table whose one field fills the stride is an
 * array of the field's type. Otherwise its element is a structure {@code S_<address>} of
 * these fields and of those that code accesses directly in the first element, named
 * {@code f<offset>}, and the table is labeled {@code tbl_<address>}. A field indexed again by
 * a smaller stride, as in a two-dimensional array, is an array that reaches the next field.
 * <p>
 * The number of elements comes from the code: comparisons of an index with a constant, as
 * in {@code i < 8}, and masks such as {@code i & 7}, the largest over all accesses (not 0xff,
 * which marks an index that is not valid). Without one, a table reaches the next element that
 * code accesses or a pointer in memory points to, within 512 bytes; if there is none, an
 * array of structures has one element (for the decompiler to show its fields) and an array
 * of a single type is not created. A table never reaches an access or data that does not fit
 * its elements (another size or offset, a structure, an array or code), or another table, and
 * never starts inside data.
 * <p>
 * Where code indexes one address with several strides, as in {@code a[i]} and
 * {@code a[2 * i]}, an array of the smallest stride whose elements all the accesses are
 * wins over a structure of the larger stride.
 * <p>
 * Fields get the type their accesses agree on, also in later rounds, when the decompiler
 * shows more; with default types, those that remain untyped get the unsigned integer of
 * their size. A loaded pointer gets the type code casts it to, and a pointer to a primitive
 * the pointer to a structure the analyzer made that starts with it. The data that pointer
 * fields point to gets the pointed-to type (see {@link E200Data#targets}).
 */
final class E200Tables {

	/** Elements of a table, and its size */
	private static final int MAX_ELEMENTS = 4096;
	private static final long MAX_SIZE = 0x10000;
	/** Bytes in which the end of a table with no bound in the code is looked for */
	private static final long MAX_UNBOUNDED_SIZE = 512;

	/**
	 * A load or store of {@code size} bytes, the value having {@code type}, at a constant
	 * address plus an index times {@code stride}, or at the address if the stride is 0;
	 * {@code inner} is the stride of a second, smaller index (0 if none) and {@code bound}
	 * the number of elements the code allows (0 if unknown).
	 */
	record Access(Address address, int size, DataType type, long stride, long inner, int bound) {}

	/** A table created */
	private record Table(Address start, long stride, int count) {
		long length() {
			return stride * count;
		}
	}

	private final Program program;
	private final Listing listing;
	private final ReferenceManager references;
	private final boolean signedChar;
	/** The tables created, by address */
	private final TreeMap<Address, Table> tables = new TreeMap<>();
	/** The values of the aligned words of initialized memory that are addresses in memory */
	private Set<Address> pointers;

	E200Tables(Program program) {
		this.program = program;
		this.listing = program.getListing();
		this.references = program.getReferenceManager();
		this.signedChar = program.getDataTypeManager().getDataOrganization().isSignedChar();
	}

	// ---- Collection ---------------------------------------------------------------------------

	/** The loads and stores at a constant address, plus an index or not, of a function */
	static List<Access> collect(HighFunction high) {
		List<Access> accesses = new ArrayList<>();
		Program program = high.getFunction().getProgram();
		AddressSpace space = program.getAddressFactory().getDefaultAddressSpace();
		Iterator<PcodeOpAST> ops = high.getPcodeOps();
		while (ops.hasNext()) {
			PcodeOpAST op = ops.next();
			int opcode = op.getOpcode();
			if (opcode != PcodeOp.LOAD && opcode != PcodeOp.STORE) {
				continue;
			}
			Varnode value = opcode == PcodeOp.LOAD ? op.getOutput() : op.getInput(2);
			Sum sum = new Sum();
			add(op.getInput(1), 1, false, sum, 0);
			long constant = sum.constant & space.getMaxAddress().getOffset();
			if (value == null || !sum.ok || constant == 0) {
				continue;
			}
			int size = value.getSize();
			Term main = null;
			for (Term t : sum.terms) {
				if (main == null || t.scale() > main.scale()) {
					main = t;
				}
			}
			long inner = 0;
			boolean ok = main == null || main.scale() >= size;
			for (Term t : sum.terms) {
				if (t != main) {
					ok &= t.scale() >= size;
					inner = Math.max(inner, t.scale());
				}
			}
			Address address = space.getAddress(constant);
			if (!ok || program.getMemory().getBlock(address) == null) {
				continue;
			}
			DataType type = E200Integers.of(value.getHigh());
			boolean open = !E200Types.informative(type);
			if (opcode == PcodeOp.LOAD && (open || type instanceof Pointer)) {
				DataType cast = E200Code.castTo(value); // what code takes a loaded pointer for
				if (cast != null && (open || E200Types.ownStructurePointer(cast))) {
					type = cast;
				}
			}
			accesses.add(main == null ? new Access(address, size, type, 0, 0, 0)
					: new Access(address, size, type, main.scale(),
						inner == main.scale() ? 0 : inner, bound(main.index())));
		}
		return accesses;
	}

	/** An address as a constant (modulo the address size) plus indexes times their strides */
	private static final class Sum {
		long constant;
		List<Term> terms = new ArrayList<>();
		boolean ok = true;
	}

	private record Term(Varnode index, long scale) {}

	/**
	 * Adds {@code v} times {@code scale} to {@code sum}. In an index, constants are left out:
	 * {@code (&X)[i + 1]} is an access of the array at {@code X}.
	 */
	private static void add(Varnode v, long scale, boolean index, Sum sum, int depth) {
		if (depth > 8 || scale <= 0) {
			sum.ok = false;
			return;
		}
		if (v.isConstant()) {
			if (!index) {
				sum.constant += v.getOffset() * scale;
			}
			return;
		}
		PcodeOp def = v.getDef();
		if (def != null) {
			switch (def.getOpcode()) {
				case PcodeOp.INT_ADD:
					add(def.getInput(0), scale, index, sum, depth + 1);
					add(def.getInput(1), scale, index, sum, depth + 1);
					return;
				case PcodeOp.PTRADD: // (&X)[i], an index and the element size
					if (def.getInput(2).isConstant()) {
						add(def.getInput(0), scale, index, sum, depth + 1);
						add(def.getInput(1), scale * def.getInput(2).getOffset(), true, sum,
							depth + 1);
						return;
					}
					break;
				case PcodeOp.PTRSUB: // &X, or a field of a structure
					add(def.getInput(0), scale, index, sum, depth + 1);
					add(def.getInput(1), scale, index, sum, depth + 1);
					return;
				case PcodeOp.INT_MULT:
					if (def.getInput(1).isConstant() != def.getInput(0).isConstant()) {
						boolean second = def.getInput(1).isConstant();
						Varnode k = def.getInput(second ? 1 : 0);
						add(def.getInput(second ? 0 : 1), scale * k.getOffset(), true, sum,
							depth + 1);
						return;
					}
					break;
				case PcodeOp.INT_LEFT:
					if (def.getInput(1).isConstant() && def.getInput(1).getOffset() < 16) {
						add(def.getInput(0), scale << def.getInput(1).getOffset(), true, sum,
							depth + 1);
						return;
					}
					break;
				case PcodeOp.CAST:
				case PcodeOp.COPY:
				case PcodeOp.INT_ZEXT:
				case PcodeOp.INT_SEXT:
					add(def.getInput(0), scale, index, sum, depth + 1);
					return;
				default:
					break;
			}
		}
		sum.terms.add(new Term(v, scale));
	}

	/**
	 * The number of elements an index can reach, from the comparisons of it with a constant
	 * and masks of it, the largest; 0 if none gives at least two.
	 */
	private static int bound(Varnode index) {
		int bound = 0;
		Deque<Varnode> todo = new ArrayDeque<>();
		Set<Object> seen = new HashSet<>();
		todo.add(index);
		while (!todo.isEmpty()) {
			Varnode v = todo.pop();
			HighVariable high = v.getHigh();
			if (!seen.add(high != null ? high : v)) {
				continue;
			}
			Varnode[] instances = high != null ? high.getInstances() : new Varnode[] { v };
			for (Varnode instance : instances) {
				PcodeOp def = instance.getDef();
				if (def != null) {
					switch (def.getOpcode()) {
						case PcodeOp.INT_ZEXT, PcodeOp.INT_SEXT, PcodeOp.CAST, PcodeOp.COPY ->
							todo.add(def.getInput(0));
						case PcodeOp.INT_AND -> bound = Math.max(bound, mask(def));
						default -> {
						}
					}
				}
				Iterator<PcodeOp> uses = instance.getDescendants();
				while (uses.hasNext()) {
					PcodeOp use = uses.next();
					switch (use.getOpcode()) {
						case PcodeOp.INT_ZEXT, PcodeOp.INT_SEXT, PcodeOp.CAST, PcodeOp.COPY -> {
							if (use.getOutput() != null) {
								todo.add(use.getOutput());
							}
						}
						default -> bound = Math.max(bound, compared(use, instance));
					}
				}
			}
		}
		return bound >= 2 && bound <= MAX_ELEMENTS ? bound : 0;
	}

	/**
	 * The elements an index masked with 2^n - 1 can reach; not for 0xff and 0xffff, which
	 * narrow a value to a char or short
	 */
	private static int mask(PcodeOp and) {
		for (int i = 0; i < 2; i++) {
			Varnode k = and.getInput(i);
			if (k.isConstant() && k.getOffset() > 0 && k.getOffset() < 0xff &&
				(k.getOffset() & (k.getOffset() + 1)) == 0) {
				return (int) k.getOffset() + 1;
			}
		}
		return 0;
	}

	/** The elements a comparison of {@code v} with a constant allows, or 0 */
	private static int compared(PcodeOp op, Varnode v) {
		if (op.getNumInputs() != 2) {
			return 0;
		}
		boolean left = op.getInput(0) == v;
		Varnode other = op.getInput(left ? 1 : 0);
		if (!other.isConstant() || E200Code.signed(other) <= 0 ||
			E200Code.signed(other) >= MAX_ELEMENTS) {
			return 0;
		}
		int k = (int) E200Code.signed(other);
		if (k == 0xfe || k == 0xff || k == 0x100) {
			return 0; // 0xff marks an index that is not valid, not the end of a table
		}
		return switch (op.getOpcode()) {
			// i < k, k <= i: k elements; i <= k, k < i: k + 1
			case PcodeOp.INT_LESS, PcodeOp.INT_SLESS -> left ? k : k + 1;
			case PcodeOp.INT_LESSEQUAL, PcodeOp.INT_SLESSEQUAL -> left ? k + 1 : k;
			case PcodeOp.INT_EQUAL, PcodeOp.INT_NOTEQUAL -> k;
			default -> 0;
		};
	}

	// ---- Tables -------------------------------------------------------------------------------

	/**
	 * Types the fields of the tables created before from the accesses, creates the tables
	 * that the accesses show where there are none and, with {@code defaults}, gives the
	 * fields that remain untyped the unsigned integer of their size.
	 *
	 * @param accesses the accesses in all decompiled functions
	 * @param changed gets the addresses of the fields created or typed
	 * @return the number of tables created
	 */
	int update(Collection<Access> accesses, boolean defaults, Set<Address> changed,
			TaskMonitor monitor) throws CancelledException {
		TreeMap<Address, List<Access>> direct = new TreeMap<>();
		TreeMap<Long, TreeMap<Address, List<Access>>> byStride = new TreeMap<>();
		Map<Table, TreeMap<Long, List<DataType>>> fieldTypes = new HashMap<>();
		for (Access a : accesses) {
			monitor.checkCancelled();
			Table table = tableContaining(a.address());
			if (table != null) {
				long offset = a.address().subtract(table.start()) % table.stride();
				if ((a.stride() == 0 || a.stride() == table.stride()) && a.type() != null &&
					!Undefined.isUndefined(a.type()) && a.type().getLength() == a.size()) {
					fieldTypes.computeIfAbsent(table, t -> new TreeMap<>())
							.computeIfAbsent(offset, o -> new ArrayList<>())
							.add(a.type());
				}
				continue;
			}
			if (a.stride() == 0) {
				direct.computeIfAbsent(a.address(), x -> new ArrayList<>()).add(a);
			}
			else {
				byStride.computeIfAbsent(a.stride(), s -> new TreeMap<>())
						.computeIfAbsent(a.address(), x -> new ArrayList<>())
						.add(a);
			}
		}
		for (Map.Entry<Table, TreeMap<Long, List<DataType>>> e : fieldTypes.entrySet()) {
			monitor.checkCancelled();
			for (Map.Entry<Long, List<DataType>> f : e.getValue().entrySet()) {
				DataType type =
					E200Types.chooseType(pointerTypes(f.getValue()), signedChar, true);
				if (type != null && retype(e.getKey(), f.getKey(), type)) {
					changed.add(e.getKey().start().add(f.getKey()));
				}
			}
		}
		int created = create(byStride, direct, changed, monitor);
		if (defaults) {
			for (Table table : tables.values()) {
				monitor.checkCancelled();
				Structure structure = structure(table);
				List<Long> offsets = new ArrayList<>();
				if (structure == null) {
					offsets.add(0L);
				}
				else {
					for (DataTypeComponent c : structure.getDefinedComponents()) {
						offsets.add((long) c.getOffset());
					}
				}
				for (long offset : offsets) {
					DataType type = fieldType(table, offset);
					if (type != null && Undefined.isUndefined(type) &&
						retype(table, offset, E200Types.unsigned(type.getLength()))) {
						changed.add(table.start().add(offset));
					}
				}
			}
		}
		return created;
	}

	/**
	 * Whether an address is in a table whose field there has no type or points to undefined,
	 * which the decompiled code may show more of
	 */
	boolean openField(Address address) {
		Table table = tableContaining(address);
		if (table == null) {
			return false;
		}
		DataType type = fieldType(table, address.subtract(table.start()) % table.stride());
		return type != null && (Undefined.isUndefined(type) ||
			type instanceof Pointer && !E200Types.informative(type));
	}

	private Table tableContaining(Address address) {
		Map.Entry<Address, Table> e = tables.floorEntry(address);
		return e != null && address.subtract(e.getKey()) < e.getValue().length() ? e.getValue()
				: null;
	}

	/** The structure of a table's elements, or null for an array of a single type */
	private Structure structure(Table table) {
		Data data = listing.getDataAt(table.start());
		if (data != null && data.getDataType() instanceof Array array &&
			array.getDataType() instanceof Structure s) {
			return s;
		}
		return null;
	}

	/** The type of the field at {@code offset} of a table's element (its elements' if an array) */
	private DataType fieldType(Table table, long offset) {
		Data data = listing.getDataAt(table.start());
		if (data == null || !(data.getDataType() instanceof Array array)) {
			return null;
		}
		DataType type = array.getDataType();
		if (type instanceof Structure s) {
			DataTypeComponent c = s.getComponentAt((int) offset);
			type = c == null || c.getDataType() instanceof DefaultDataType ? null
					: c.getDataType();
		}
		else if (offset != 0) {
			return null;
		}
		return type instanceof Array a ? a.getDataType() : type;
	}

	/**
	 * The types of a field's accesses that say most about a pointer: pointers to a structure
	 * the analyzer created rather than to what it starts with, and pointers to a type rather
	 * than to undefined, as code casts a loaded {@code undefined *} where it knows more
	 */
	private static List<DataType> pointerTypes(List<DataType> types) {
		List<DataType> structures = new ArrayList<>();
		List<DataType> typed = new ArrayList<>();
		for (DataType t : types) {
			if (E200Types.ownStructurePointer(t)) {
				structures.add(t);
			}
			if (!(t instanceof Pointer) || E200Types.informative(t)) {
				typed.add(t);
			}
		}
		if (!structures.isEmpty()) {
			return structures;
		}
		return typed.size() < types.size() &&
			typed.stream().anyMatch(t -> t instanceof Pointer) ? typed : types;
	}

	/**
	 * Whether {@code type} says more than a field's {@code current} type: undefined, a pointer
	 * to undefined, or a pointer to what a structure the analyzer created starts with, which
	 * {@code type} points to
	 */
	private static boolean refines(DataType current, DataType type) {
		if (Undefined.isUndefined(current)) {
			return true;
		}
		if (!(current instanceof Pointer p) || !(type instanceof Pointer q) ||
			!E200Types.informative(type)) {
			return false;
		}
		if (!E200Types.informative(current)) {
			return true;
		}
		DataType target = p.getDataType();
		if (target instanceof Composite || !E200Types.ownStructurePointer(q)) {
			return false;
		}
		DataTypeComponent first = ((Structure) q.getDataType()).getComponentAt(0);
		return first != null && !(first.getDataType() instanceof DefaultDataType) &&
			first.getLength() == target.getLength();
	}

	/**
	 * Gives the field at {@code offset} of a table's elements {@code type} if that says more
	 * (see {@link #refines}) and has its size (or its elements if the field is an array);
	 * returns whether it did.
	 */
	private boolean retype(Table table, long offset, DataType type) {
		DataType current = fieldType(table, offset);
		if (current == null || !refines(current, type) ||
			current.getLength() != type.getLength()) {
			return false;
		}
		Structure structure = structure(table);
		if (structure != null) {
			DataTypeComponent c = structure.getComponentAt((int) offset);
			DataType replacement = c.getDataType() instanceof Array a
					? new ArrayDataType(type, a.getNumElements(), type.getLength())
					: type;
			structure.replaceAtOffset((int) offset, replacement, replacement.getLength(),
				c.getFieldName(), null);
			E200Data.targets(program, listing.getDataAt(table.start()), 0);
			return true;
		}
		Data data = listing.getDataAt(table.start());
		DataType element = ((Array) data.getDataType()).getDataType() instanceof Array a
				? new ArrayDataType(type, a.getNumElements(), type.getLength())
				: type;
		if (!E200Data.replace(listing, table.start(),
			new ArrayDataType(element, table.count(), (int) table.stride()))) {
			return false;
		}
		E200Data.targets(program, listing.getDataAt(table.start()), 0);
		return true;
	}

	/** Creates the tables that the indexed accesses show; returns how many. */
	private int create(TreeMap<Long, TreeMap<Address, List<Access>>> byStride,
			TreeMap<Address, List<Access>> direct, Set<Address> changed, TaskMonitor monitor)
			throws CancelledException {
		List<Cluster> clusters = new ArrayList<>();
		for (Map.Entry<Long, TreeMap<Address, List<Access>>> e : byStride.entrySet()) {
			long stride = e.getKey();
			Cluster current = null;
			for (Map.Entry<Address, List<Access>> f : e.getValue().entrySet()) {
				if (current == null || f.getKey().subtract(current.start) >= stride) {
					current = new Cluster(f.getKey(), stride);
					clusters.add(current);
				}
				current.fields.put(f.getKey().subtract(current.start), f.getValue());
			}
		}
		// larger tables first where several start at one address
		clusters.sort(Comparator.comparing((Cluster c) -> c.start)
				.thenComparing(c -> -c.stride));
		Set<Address> starts = new HashSet<>();
		for (Cluster c : clusters) {
			starts.add(c.start);
		}
		Set<Cluster> covered = covered(clusters);
		int created = 0;
		for (Cluster c : clusters) {
			monitor.checkCancelled();
			if (covered.contains(c) || tableContaining(c.start) != null) {
				continue;
			}
			Table table = c.create(starts, direct);
			if (table != null) {
				tables.put(table.start(), table);
				for (Long offset : c.layoutOffsets) {
					changed.add(table.start().add(offset));
				}
				created++;
			}
		}
		return created;
	}

	/**
	 * The clusters that an array of a single type at the same start covers: code that indexes
	 * one place with several strides, as in {@code a[i]} and {@code a[2 * i]}, accesses an
	 * array of the smallest stride when all the accesses are its elements, not a structure of
	 * the larger one. The covering array takes over their bounds.
	 */
	private static Set<Cluster> covered(List<Cluster> clusters) {
		Set<Cluster> covered = new HashSet<>();
		Map<Address, List<Cluster>> byStart = new HashMap<>();
		for (Cluster c : clusters) {
			byStart.computeIfAbsent(c.start, a -> new ArrayList<>()).add(c);
		}
		for (List<Cluster> group : byStart.values()) {
			Cluster fine = null;
			for (Cluster c : group) {
				if (c.elementsOf(c.stride) && (fine == null || c.stride < fine.stride)) {
					fine = c;
				}
			}
			for (Cluster c : group) {
				if (fine != null && c != fine && c.stride % fine.stride == 0 &&
					c.elementsOf(fine.stride)) {
					covered.add(c);
					fine.coveredBound = Math.max(fine.coveredBound,
						(int) Math.min(MAX_ELEMENTS, c.bound() * (c.stride / fine.stride)));
				}
			}
		}
		return covered;
	}

	/** The accesses of one table, by the offset of their field in the element */
	private final class Cluster {
		final Address start;
		final long stride;
		final TreeMap<Long, List<Access>> fields = new TreeMap<>();
		final List<Long> layoutOffsets = new ArrayList<>();
		/** The bound of the clusters this one covers, in its elements */
		int coveredBound;

		Cluster(Address start, long stride) {
			this.start = start;
			this.stride = stride;
		}

		Table create(Set<Address> starts, TreeMap<Address, List<Access>> direct) {
			MemoryBlock block = program.getMemory().getBlock(start);
			if (block == null || block.isVolatile() ||
				program.getFunctionManager().getFunctionContaining(start) != null) {
				return null;
			}
			Data existing = listing.getDataContaining(start);
			if (existing != null && (!E200Types.primitive(existing.getDataType()) ||
				!existing.getAddress().equals(start))) {
				return null; // an array or structure already, or inside other data
			}
			int bound = Math.max(bound(), coveredBound);
			TreeMap<Long, DataType> layout = layout();
			if (layout == null) {
				return null;
			}
			long max =
				bound > 0 ? Math.min(bound, MAX_SIZE / stride) : MAX_UNBOUNDED_SIZE / stride;
			max = Math.min(max, (block.getEnd().subtract(start) + 1) / stride);
			if (max < 1) {
				return null;
			}
			boolean single = layout.size() == 1 && layout.firstKey() == 0 &&
				layout.firstEntry().getValue().getLength() == stride;
			if (!single) {
				// fields that code only accesses directly, in the first element or those the
				// bound allows
				addDirectFields(layout, bound > 0 ? max : 1, direct);
			}
			DataType element = element(layout, single);
			if (element == null) {
				return null;
			}
			int count = count(element, single, bound, max, starts, direct);
			if (count < 1) {
				return null;
			}
			Address end = start.add(count * stride - 1);
			try {
				listing.clearCodeUnits(start, end, false);
				E200Data.targets(program, listing.createData(start,
					new ArrayDataType(element, count, (int) stride, program.getDataTypeManager())),
					0);
			}
			catch (CodeUnitInsertionException e) {
				Msg.warn(E200Analyzer.class, "Could not create a table at " + start + ": " + e);
				return null;
			}
			if (!single) {
				E200Data.label(program, start, "tbl_" + start.toString(false),
					SourceType.ANALYSIS);
			}
			layoutOffsets.addAll(layout.keySet());
			return new Table(start, stride, count);
		}

		/** The number of elements the code allows, the largest over the accesses, or 0 */
		int bound() {
			int bound = 0;
			for (List<Access> list : fields.values()) {
				for (Access a : list) {
					bound = Math.max(bound, a.bound());
				}
			}
			return bound;
		}

		/**
		 * Whether all the accesses are of {@code size} bytes at multiples of it, with no
		 * second index: elements of an array of that stride
		 */
		boolean elementsOf(long size) {
			for (Map.Entry<Long, List<Access>> e : fields.entrySet()) {
				if (e.getKey() % size != 0) {
					return false;
				}
				for (Access a : e.getValue()) {
					if (a.size() != size || a.inner() != 0) {
						return false;
					}
				}
			}
			return true;
		}

		/**
		 * The types of the fields that code indexes, by offset; a field indexed again by a
		 * smaller stride is an array reaching the next field. Null if fields overlap.
		 */
		TreeMap<Long, DataType> layout() {
			List<Long> offsets = new ArrayList<>(fields.keySet());
			TreeMap<Long, DataType> layout = new TreeMap<>();
			for (int i = 0; i < offsets.size(); i++) {
				long offset = offsets.get(i);
				long next = i + 1 < offsets.size() ? offsets.get(i + 1) : stride;
				DataType type = field(fields.get(offset));
				if (type == null || offset + type.getLength() > next) {
					return null;
				}
				long inner = 0;
				for (Access a : fields.get(offset)) {
					inner = Math.max(inner, a.inner());
				}
				if (inner == type.getLength() && next - offset >= 2 * inner) {
					type = new ArrayDataType(type, (int) ((next - offset) / inner),
						type.getLength());
				}
				layout.put(offset, type);
			}
			return layout;
		}

		/** The type of a field from its accesses: the size they agree on, typed if they agree */
		private DataType field(List<Access> accesses) {
			int size = 0;
			List<DataType> types = new ArrayList<>();
			boolean untyped = false;
			for (Access a : accesses) {
				if (size != 0 && a.size() != size) {
					return null;
				}
				size = a.size();
				if (a.type() != null && !Undefined.isUndefined(a.type()) &&
					a.type().getLength() == size) {
					types.add(a.type());
				}
				else {
					untyped = true;
				}
			}
			DataType type = types.isEmpty() || untyped ? null
					: E200Types.chooseType(pointerTypes(types), signedChar, true);
			return type != null && type.getLength() == size ? type
					: Undefined.getUndefinedDataType(size);
		}

		/**
		 * Adds the fields that code accesses directly in the first {@code elements} elements
		 * where no field is, of the size of the accesses.
		 */
		void addDirectFields(TreeMap<Long, DataType> layout, long elements,
				TreeMap<Address, List<Access>> direct) {
			Address end = start.add(elements * stride - 1);
			TreeMap<Long, Integer> sizes = new TreeMap<>();
			for (Map.Entry<Address, List<Access>> e : direct.subMap(start, true, end, true)
					.entrySet()) {
				for (Access a : e.getValue()) {
					sizes.merge(e.getKey().subtract(start) % stride, a.size(),
						(x, y) -> x.equals(y) ? x : -1);
				}
			}
			AddressIterator it =
				references.getReferenceDestinationIterator(new AddressSet(start, end), true);
			while (it.hasNext()) {
				Address a = it.next();
				for (Reference ref : references.getReferencesTo(a)) {
					int size = E200Code.accessSize(listing.getInstructionAt(ref.getFromAddress()));
					if (size > 0) {
						sizes.merge(a.subtract(start) % stride, size,
							(x, y) -> x.equals(y) ? x : -1);
					}
				}
			}
			for (Map.Entry<Long, Integer> e : sizes.entrySet()) {
				long offset = e.getKey();
				int size = e.getValue();
				Map.Entry<Long, DataType> before = layout.floorEntry(offset);
				Long after = layout.higherKey(offset);
				if (size <= 0 || offset + size > stride ||
					before != null && before.getKey() + before.getValue().getLength() > offset ||
					after != null && offset + size > after) {
					continue; // a field there already, or accesses of several sizes
				}
				Data data = listing.getDefinedDataAt(start.add(offset));
				layout.put(offset, data != null && E200Types.primitive(data.getDataType()) &&
					!Undefined.isUndefined(data.getDataType()) && data.getLength() == size
							? data.getDataType()
							: Undefined.getUndefinedDataType(size));
			}
		}

		/**
		 * The type of the elements: the one field's type if it fills the stride, otherwise a
		 * structure of the fields, named after the table.
		 */
		DataType element(TreeMap<Long, DataType> layout, boolean single) {
			if (single) {
				return layout.get(0L);
			}
			DataTypeManager manager = program.getDataTypeManager();
			String name = "S_" + start.toString(false);
			StructureDataType structure =
				new StructureDataType(E200Types.CATEGORY, name, (int) stride, manager);
			for (Map.Entry<Long, DataType> e : layout.entrySet()) {
				structure.replaceAtOffset(e.getKey().intValue(), e.getValue(),
					e.getValue().getLength(), "f" + Long.toHexString(e.getKey()), null);
			}
			DataType old = manager.getDataType(E200Types.CATEGORY, name);
			if (old != null) {
				if (old.isEquivalent(structure)) {
					return old;
				}
				try {
					structure.setName(manager.getUniqueName(E200Types.CATEGORY, name));
				}
				catch (InvalidNameException e) {
					return null;
				}
			}
			return manager.addDataType(structure, DataTypeConflictHandler.DEFAULT_HANDLER);
		}

		/**
		 * The number of elements: up to the bound if there is one, otherwise to the next
		 * element accessed or pointed to; never past an access, data or code that does not
		 * fit, or another table.
		 */
		int count(DataType element, boolean single, int bound, long max,
				Set<Address> starts, TreeMap<Address, List<Access>> direct) {
			Address end = start.add(max * stride - 1);
			AddressSet range = new AddressSet(start, end);
			long conflict = max; // the first element with something that does not fit
			InstructionIterator code = listing.getInstructions(range, true);
			if (code.hasNext()) {
				conflict = index(code.next().getAddress());
			}
			for (Data data : listing.getDefinedData(range, true)) {
				if (!E200Types.primitive(data.getDataType()) ||
					!fits(element, offset(data.getAddress()), data.getLength())) {
					conflict = Math.min(conflict, index(data.getAddress()));
					break;
				}
			}
			for (Address other : starts) {
				if (!other.equals(start) && range.contains(other)) {
					conflict = Math.min(conflict, index(other)); // another table
				}
			}
			// what code accesses directly, from the listing and the decompiler
			TreeMap<Address, List<Integer>> accessed = new TreeMap<>();
			for (Map.Entry<Address, List<Access>> e : direct.subMap(start, true, end, true)
					.entrySet()) {
				for (Access a : e.getValue()) {
					accessed.computeIfAbsent(e.getKey(), x -> new ArrayList<>()).add(a.size());
				}
			}
			AddressIterator it = references.getReferenceDestinationIterator(range, true);
			while (it.hasNext()) {
				Address a = it.next();
				for (Reference ref : references.getReferencesTo(a)) {
					accessed.computeIfAbsent(a, x -> new ArrayList<>())
							.add(E200Code.accessSize(listing.getInstructionAt(ref.getFromAddress())));
				}
			}
			// pointers in data that is not typed yet, as in configuration tables
			for (Address a : pointers()) {
				if (range.contains(a)) {
					accessed.computeIfAbsent(a, x -> new ArrayList<>()).add(0);
				}
			}
			for (Map.Entry<Address, List<Integer>> e : accessed.entrySet()) {
				long index = index(e.getKey());
				if (index >= conflict) {
					break;
				}
				if (index > 0 && bound == 0) {
					conflict = index; // another variable, or an element used on its own
					break;
				}
				boolean fits = true;
				for (int size : e.getValue()) {
					fits &= fits(element, offset(e.getKey()), size);
				}
				if (!fits) {
					conflict = index;
					break;
				}
			}
			if (conflict == 0) {
				return 0;
			}
			if (bound == 0 && conflict == max) {
				// nothing ends an array of unknown length; an array of structures keeps an
				// element, for the decompiler to show its fields
				return single ? 0 : 1;
			}
			return (int) conflict;
		}

		private long index(Address a) {
			return a.subtract(start) / stride;
		}

		private long offset(Address a) {
			return a.subtract(start) % stride;
		}
	}

	/**
	 * The addresses that aligned words of initialized memory hold, outside code: pointers to
	 * variables that code may only reach through them
	 */
	private Set<Address> pointers() {
		if (pointers != null) {
			return pointers;
		}
		pointers = new HashSet<>();
		Memory memory = program.getMemory();
		AddressSpace space = program.getAddressFactory().getDefaultAddressSpace();
		for (MemoryBlock block : memory.getBlocks()) {
			if (!block.isInitialized() || block.isVolatile()) {
				continue;
			}
			byte[] bytes = new byte[(int) Math.min(block.getSize(), Integer.MAX_VALUE)];
			try {
				block.getBytes(block.getStart(), bytes);
			}
			catch (MemoryAccessException e) {
				continue;
			}
			long base = block.getStart().getOffset();
			boolean big = memory.isBigEndian();
			for (int i = (int) ((4 - base % 4) % 4); i + 4 <= bytes.length; i += 4) {
				long value = big
						? (bytes[i] & 0xffL) << 24 | (bytes[i + 1] & 0xffL) << 16 |
							(bytes[i + 2] & 0xffL) << 8 | bytes[i + 3] & 0xffL
						: (bytes[i + 3] & 0xffL) << 24 | (bytes[i + 2] & 0xffL) << 16 |
							(bytes[i + 1] & 0xffL) << 8 | bytes[i] & 0xffL;
				if (value == 0 || value == 0xffffffffL) {
					continue;
				}
				Address target = space.getAddress(value);
				if (memory.contains(target) &&
					listing.getInstructionContaining(block.getStart().add(i)) == null) {
					pointers.add(target);
				}
			}
		}
		return pointers;
	}

	/** Whether an access of {@code size} bytes (0: the address only) at {@code offset} fits */
	private static boolean fits(DataType element, long offset, int size) {
		DataType type = element;
		while (true) {
			if (type instanceof TypeDef t) {
				type = t.getBaseDataType();
			}
			if (type instanceof Structure s) {
				DataTypeComponent c = s.getComponentContaining((int) offset);
				if (c == null || c.getDataType() instanceof DefaultDataType) {
					return false;
				}
				offset -= c.getOffset();
				type = c.getDataType();
			}
			else if (type instanceof Array a) {
				offset %= a.getElementLength();
				type = a.getDataType();
			}
			else {
				return offset == 0 && (size == 0 || size == type.getLength());
			}
		}
	}
}
