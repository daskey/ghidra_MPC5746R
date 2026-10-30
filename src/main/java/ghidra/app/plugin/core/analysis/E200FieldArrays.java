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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Arrays that the pointer fields of structures point to (part of {@link E200DataTypes}).
 * <p>
 * A descriptor in flash, as of a calibration map, holds the lengths of the arrays it points
 * to: {@code {short nx; short ny; float *x; float *y; void *values; byte type}}. The lookup
 * function indexes the arrays with bounds it reads from the descriptor, so no array has a
 * length in the code, and {@link E200Data#targets} gives each pointer's target a single
 * element. The instances of the structure show the arrays instead: the data at the target
 * of a pointer field reaches the next address that a pointer in memory points to, that code
 * references or that holds data or code, and the gap is the array.
 * <p>
 * The count field of the pointer field is the field the code indexes the array by, which
 * E200Structures finds in the code that reads the structure ({@code p->x[p->n - 1]}) and
 * records in the field's comment ({@code f0 * f2 elements}); where the code shows none, an
 * integer field of the structure whose value is the number of elements in the gap at most
 * instances, or the product of two such fields, is taken for it, and recorded the same
 * way. The count gives the length where the gap holds padding. A pointer field whose element type the code chooses at run
 * time, casting the pointer to several types, gets at each instance the type whose size
 * fits the gap, and an integer field whose value says which size, at the instances where
 * one fits, is its selector ({@code element size by f10}); the sizes the code gives the
 * selector's values, where it compares the selector with constants on the way to the casts,
 * come with the structure ({@code element size by f10: 0=4, 4=1, 8=2}). The comments of a structure
 * built in an earlier analysis are used as they are. Stray instructions in the way, of no
 * function and with nothing flowing to them, are data that was disassembled, and where a
 * count field gives the length, so are the strings the string analysis made of the values,
 * the words in the array or in other arrays of values that happen to be addresses, and the
 * arrays of integers that code reading a region word by word made over the array, which are
 * carved around it.
 */
final class E200FieldArrays {

	/** Longest array, in bytes */
	private static final long MAX_BYTES = 0x10000;
	/** Instances an inference needs, and the share of the instances it must hold for */
	private static final int MIN_INSTANCES = 4;
	private static final double MIN_SHARE = 0.5;
	/** The share of the instances of a selector value that must agree on the size */
	private static final double MIN_AGREEMENT = 0.8;

	private static final Pattern ELEMENTS =
		Pattern.compile("\\bf([0-9a-f]+)(?: \\* f([0-9a-f]+))? elements\\b");
	private static final Pattern SELECTOR = Pattern.compile(
		"\\belement size by f([0-9a-f]+)(?::((?: [0-9a-f]+=[0-9]+,?)+))?");
	private static final Pattern CASTS = Pattern.compile("\\bcast to ([^;]+)");

	private E200FieldArrays() {
	}

	/**
	 * Creates the arrays that the pointer fields of the analyzer's structures point to, at
	 * all instances of the structures in flash; returns how many.
	 */
	static int apply(Program program, TaskMonitor monitor) throws CancelledException {
		// the data the pointer fields point to, for the fields typed after their instances
		// were created, as a pointer to a descriptor in a configuration structure
		for (List<Data> data : instances(program, monitor).values()) {
			for (Data instance : data) {
				monitor.checkCancelled();
				E200Data.targets(program, instance, 0);
			}
		}
		Boundaries boundaries = new Boundaries(program);
		int created = 0;
		for (Map.Entry<Structure, List<Data>> e : instances(program, monitor).entrySet()) {
			monitor.checkCancelled();
			Structure s = e.getKey();
			for (DataTypeComponent c : s.getDefinedComponents()) {
				if (!(c.getDataType() instanceof Pointer p) || c.getLength() != 4) {
					continue;
				}
				PointerField field = new PointerField(program, s, c, p, e.getValue(), boundaries);
				if (field.instances.size() < 1 || field.sizes.isEmpty()) {
					continue;
				}
				field.infer();
				field.describe();
				created += field.createArrays();
			}
		}
		return created;
	}

	/** The instances of each structure of the analyzer's in flash: data, and array elements */
	private static Map<Structure, List<Data>> instances(Program program, TaskMonitor monitor)
			throws CancelledException {
		Listing listing = program.getListing();
		Map<Structure, List<Data>> instances = new LinkedHashMap<>();
		for (MemoryBlock block : program.getMemory().getBlocks()) {
			if (!block.isInitialized() || block.isVolatile()) {
				continue;
			}
			DataIterator it = listing.getDefinedData(block.getStart(), true);
			while (it.hasNext()) {
				monitor.checkCancelled();
				Data data = it.next();
				if (data.getAddress().compareTo(block.getEnd()) > 0) {
					break;
				}
				DataType type = data.getDataType();
				if (type instanceof Array array && E200Types.ownStructure(array.getDataType())) {
					for (int i = 0; i < data.getNumComponents(); i++) {
						instances.computeIfAbsent((Structure) array.getDataType(),
							k -> new ArrayList<>()).add(data.getComponent(i));
					}
				}
				else if (E200Types.ownStructure(type)) {
					instances.computeIfAbsent((Structure) type, k -> new ArrayList<>()).add(data);
				}
			}
		}
		return instances;
	}

	/** The number of elements a field, or the product of two fields, gives */
	private record Count(int a, int b) {
		long of(Data instance) {
			long n = value(instance, a);
			if (n < 0 || b < 0) {
				return n;
			}
			long m = value(instance, b);
			return m < 0 ? -1 : n * m;
		}

		String describe() {
			return "f" + Integer.toHexString(a) +
				(b < 0 ? "" : " * f" + Integer.toHexString(b)) + " elements";
		}
	}

	/**
	 * An instance's pointer field: the instance, the target, the gap to the next thing, and
	 * the limit an array may reach: the next pointer target, code, or data that is no single
	 * value (code may reference an element of an array, or have created a value in it)
	 */
	private record Instance(Data data, Address target, MemoryBlock block, long gap, long limit) {}

	/** The unsigned value of the integer field at an offset of an instance, or -1 */
	private static long value(Data instance, int offset) {
		Data field = instance.getComponentContaining(offset);
		if (field == null || field.getParentOffset() != offset ||
			!(field.getValue() instanceof Scalar s)) {
			return -1;
		}
		return s.getUnsignedValue();
	}

	/** A pointer field of a structure, with what its instances show */
	private static final class PointerField {
		private final Program program;
		private final Structure structure;
		private final DataTypeComponent component;
		private final Boundaries boundaries;
		/** The element type, or null when the code chooses it at run time */
		private final DataType element;
		/** The types the code casts the pointer to, when it chooses */
		private final List<DataType> casts = new ArrayList<>();
		/** The element sizes that come into question */
		final Set<Integer> sizes = new TreeSet<>();
		/** The integer fields of the structure, by offset */
		private final List<Integer> integers = new ArrayList<>();
		final List<Instance> instances = new ArrayList<>();
		private Count count;
		private Integer selector;
		/** The element size each value of the selector field gives */
		private final Map<Long, Integer> sizeBySelector = new HashMap<>();

		PointerField(Program program, Structure structure, DataTypeComponent component,
				Pointer pointer, List<Data> data, Boundaries boundaries) {
			this.program = program;
			this.structure = structure;
			this.component = component;
			this.boundaries = boundaries;
			DataType target = pointer.getDataType();
			// undefined1, undefined2 and undefined4 have a size, if no type
			boolean open = target == null || target instanceof VoidDataType ||
				target instanceof DefaultDataType || target.getLength() <= 0;
			element = open ? null : target;
			String comment = component.getComment() == null ? "" : component.getComment();
			if (open) {
				Matcher m = CASTS.matcher(comment);
				if (m.find()) {
					for (String name : m.group(1).split(",")) {
						DataType t = program.getDataTypeManager().getDataType(name.trim());
						if (t != null && t.getLength() > 0) {
							casts.add(t);
						}
					}
				}
				for (DataType t : casts) {
					sizes.add(t.getLength());
				}
			}
			else if (target.getLength() > 0) {
				sizes.add(target.getLength());
			}
			for (DataTypeComponent c : structure.getDefinedComponents()) {
				DataType t = c.getDataType();
				if (c.getOffset() != component.getOffset() && !(t instanceof Pointer) &&
					(E200Types.integer(t) || Undefined.isUndefined(t)) &&
					(c.getLength() == 1 || c.getLength() == 2 || c.getLength() == 4)) {
					integers.add(c.getOffset());
				}
			}
			Matcher m = ELEMENTS.matcher(comment);
			if (m.find()) {
				int a = Integer.parseInt(m.group(1), 16);
				int b = m.group(2) == null ? -1 : Integer.parseInt(m.group(2), 16);
				if (integers.contains(a) && (b < 0 || integers.contains(b))) {
					count = new Count(a, b);
				}
			}
			m = SELECTOR.matcher(comment);
			if (m.find()) {
				int offset = Integer.parseInt(m.group(1), 16);
				if (integers.contains(offset)) {
					selector = offset;
					if (m.group(2) != null) {
						// the sizes the code gives the selector's values (see E200Structures)
						for (String entry : m.group(2).split(",")) {
							String[] valueAndSize = entry.trim().split("=");
							if (valueAndSize.length == 2) {
								sizeBySelector.put(Long.parseLong(valueAndSize[0], 16),
									Integer.parseInt(valueAndSize[1]));
							}
						}
					}
				}
			}
			for (Data instance : data) {
				Data field = instance.getComponentContaining(component.getOffset());
				if (field == null || field.getParentOffset() != component.getOffset() ||
					field.getLength() != 4 || !(field.getValue() instanceof Address t)) {
					continue;
				}
				MemoryBlock block = program.getMemory().getBlock(t);
				if (block == null || !block.isInitialized() || block.isVolatile()) {
					continue;
				}
				long[] bounds = boundaries.bounds(t, block);
				instances.add(new Instance(instance, t, block, bounds[0], bounds[1]));
			}
		}

		/**
		 * Infers the count field and the selector field from the instances (see the class).
		 * The count the code shows stands unless the instances contradict it: another
		 * candidate fills the gaps of more of them exactly, enough of them to infer from.
		 */
		void infer() {
			Map<Count, Integer> countVotes = new HashMap<>();
			for (Instance i : instances) {
				for (Count c : candidates()) {
					long n = c.of(i.data());
					if (n > 1 && fitsExactly(n, i.gap())) { // one element is no array
						countVotes.merge(c, 1, Integer::sum);
					}
				}
			}
			Count best = best(countVotes, instances.size());
			if (count == null ||
				best != null && countVotes.get(best) > countVotes.getOrDefault(count, 0)) {
				count = best;
			}
			if (element == null && sizes.size() > 1) {
				// the instances where one size fits say what the selector's values mean
				Map<Integer, Map<Long, Map<Integer, Integer>>> votes = new HashMap<>();
				for (Instance i : instances) {
					Integer size = fittingSize(i);
					if (size == null) {
						continue;
					}
					for (int offset : integers) {
						if (count != null && (offset == count.a() || offset == count.b())) {
							continue;
						}
						long v = value(i.data(), offset);
						if (v >= 0) {
							votes.computeIfAbsent(offset, o -> new HashMap<>())
									.computeIfAbsent(v, x -> new HashMap<>())
									.merge(size, 1, Integer::sum);
						}
					}
				}
				chooseSelector(votes);
			}
		}

		/** The count fields that come into question: each integer field, and pairs of them */
		private List<Count> candidates() {
			List<Count> candidates = new ArrayList<>();
			for (int a : integers) {
				candidates.add(new Count(a, -1));
			}
			for (int i = 0; i < integers.size(); i++) {
				for (int j = i + 1; j < integers.size(); j++) {
					candidates.add(new Count(integers.get(i), integers.get(j)));
				}
			}
			return candidates;
		}

		/** Whether {@code n} elements of one of the sizes fill a gap exactly */
		private boolean fitsExactly(long n, long gap) {
			for (int size : sizes) {
				if (n * size == gap) {
					return true;
				}
			}
			return false;
		}

		/** The one size whose elements fill the instance's gap exactly, or null */
		private Integer fittingSize(Instance i) {
			Integer fitting = null;
			for (int size : sizes) {
				boolean fits = count != null ? count.of(i.data()) * size == i.gap()
						: i.gap() % size == 0;
				if (fits) {
					if (fitting != null) {
						return null;
					}
					fitting = size;
				}
			}
			return fitting;
		}

		/** The count with the most votes, if enough instances agree; a single field before a product */
		private static Count best(Map<Count, Integer> votes, int instances) {
			Count best = null;
			int most = 0;
			for (Map.Entry<Count, Integer> e : votes.entrySet()) {
				Count c = e.getKey();
				if (e.getValue() > most || e.getValue() == most && best != null &&
					(c.b() < 0 && best.b() >= 0 || c.b() < 0 == (best.b() < 0) && c.a() < best.a())) {
					best = c;
					most = e.getValue();
				}
			}
			return most >= MIN_INSTANCES && most >= MIN_SHARE * instances ? best : null;
		}

		/**
		 * Chooses the selector field: the one whose values each agree on a size at most of
		 * their instances, covering the most instances
		 */
		private void chooseSelector(Map<Integer, Map<Long, Map<Integer, Integer>>> votes) {
			int bestCoverage = 0;
			Map<Long, Integer> bestMapping = null;
			Integer bestOffset = null;
			for (Map.Entry<Integer, Map<Long, Map<Integer, Integer>>> field : votes.entrySet()) {
				if (selector != null && !selector.equals(field.getKey())) {
					continue; // the comment names the selector; only its mapping is learned
				}
				Map<Long, Integer> mapping = new HashMap<>();
				int coverage = 0;
				boolean consistent = true;
				for (Map.Entry<Long, Map<Integer, Integer>> v : field.getValue().entrySet()) {
					int total = 0;
					int majority = 0;
					int size = 0;
					for (Map.Entry<Integer, Integer> s : v.getValue().entrySet()) {
						total += s.getValue();
						if (s.getValue() > majority) {
							majority = s.getValue();
							size = s.getKey();
						}
					}
					if (majority < MIN_AGREEMENT * total) {
						consistent = false;
						break;
					}
					mapping.put(v.getKey(), size);
					coverage += total;
				}
				if (consistent && mapping.size() > 1 && coverage >= MIN_INSTANCES &&
					coverage > bestCoverage) {
					bestCoverage = coverage;
					bestMapping = mapping;
					bestOffset = field.getKey();
				}
			}
			if (bestMapping != null) {
				selector = bestOffset;
				bestMapping.forEach(sizeBySelector::putIfAbsent);
			}
			else if (sizeBySelector.isEmpty()) {
				selector = null;
			}
		}

		/** Records the count and selector fields in the field's comment */
		void describe() {
			String comment = component.getComment() == null ? "" : component.getComment();
			Matcher counted = ELEMENTS.matcher(comment);
			if (count != null && counted.find() && !counted.group().equals(count.describe())) {
				comment = comment.replace(counted.group(), count.describe()); // the instances
			}
			List<String> parts = new ArrayList<>();
			if (!comment.isEmpty()) {
				parts.add(comment);
			}
			if (count != null && !ELEMENTS.matcher(comment).find()) {
				parts.add(count.describe());
			}
			if (selector != null && !SELECTOR.matcher(comment).find()) {
				parts.add("element size by f" + Integer.toHexString(selector));
			}
			String described = String.join("; ", parts);
			if (!described.equals(comment)) {
				structure.replaceAtOffset(component.getOffset(), component.getDataType(),
					component.getLength(), component.getFieldName(), described);
			}
		}

		/** Creates the arrays at the targets of the instances; returns how many */
		int createArrays() {
			Listing listing = program.getListing();
			int created = 0;
			for (Instance i : instances) {
				Integer size = elementSize(i);
				if (size == null) {
					continue;
				}
				long n = count != null ? count.of(i.data()) : i.gap() / size;
				if (n <= 0 || n * size > MAX_BYTES ||
					count == null && (n * size > i.limit() || i.gap() % size != 0 || n < 2)) {
					continue;
				}
				DataType type = elementType(size);
				if (type == null) {
					continue;
				}
				Address end;
				try {
					end = i.target().addNoWrap(n * size - 1);
				}
				catch (AddressOverflowException e) {
					continue;
				}
				if (!i.block().contains(end) ||
					n * size > i.limit() && !boundaries.passable(i.target(), end, i.block())) {
					continue;
				}
				List<Data> carved = free(i.target(), end, type, (int) n);
				if (carved == null) {
					continue;
				}
				try {
					List<Remainder> remainders = remainders(carved, i.target(), end);
					listing.clearCodeUnits(i.target(), end, false);
					// one element is the value at the target, of the type, not an array of one
					Data array = listing.createData(i.target(), n == 1 ? type
							: new ArrayDataType(type, (int) n, size, program.getDataTypeManager()));
					for (Remainder r : remainders) {
						r.create(listing, program.getDataTypeManager());
					}
					E200Data.targets(program, array, 0);
					created++;
				}
				catch (CodeUnitInsertionException e) {
					// something else is there
				}
			}
			return created;
		}

		/** The element size at an instance: the type's, the selector's, or the one that fits */
		private Integer elementSize(Instance i) {
			if (element != null) {
				return element.getLength();
			}
			if (selector != null) {
				Integer size = sizeBySelector.get(value(i.data(), selector));
				if (size != null) {
					return size;
				}
			}
			if (sizes.size() == 1) {
				return sizes.iterator().next();
			}
			return fittingSize(i);
		}

		/**
		 * The element type of a size: the pointed-to type, or of the casts, the unsigned
		 * integer or the float before the others
		 */
		private DataType elementType(int size) {
			if (element != null) {
				return element;
			}
			DataType chosen = null;
			for (DataType t : casts) {
				if (t.getLength() != size) {
					continue;
				}
				DataType base = t instanceof TypeDef d ? d.getBaseDataType() : t;
				if (base instanceof AbstractFloatDataType ||
					base instanceof AbstractIntegerDataType a && !a.isSigned()) {
					return t;
				}
				if (chosen == null) {
					chosen = t;
				}
			}
			return chosen;
		}

		/**
		 * Whether an array of {@code n} elements of {@code type} may be created in a range,
		 * and is not there already: nothing is there but undefined bytes, single values,
		 * elements of the type (which pointers made at the elements), stray instructions, and,
		 * where a count field gives the length, strings and arrays of integers (code reading
		 * a region word by word made them, and the parts of them carved around other arrays;
		 * they are carved around this one). Returns the arrays to carve, or null if the
		 * range is not free.
		 */
		private List<Data> free(Address start, Address end, DataType type, int n) {
			Listing listing = program.getListing();
			boolean counted = count != null;
			List<Data> carved = new ArrayList<>();
			Data at = listing.getDataContaining(start);
			if (at != null && !at.getAddress().equals(start)) {
				if (!counted || !(string(at) || integerArray(at))) {
					return null;
				}
				carved.add(at);
			}
			if (at != null && (at.getDataType() instanceof Array a && a.getNumElements() == n &&
				a.getDataType().isEquivalent(type) ||
				n == 1 && at.getDataType().isEquivalent(type))) {
				return null; // there already
			}
			AddressSet range = new AddressSet(start, end);
			if (!E200Data.strayCode(program, range)) {
				return null;
			}
			for (Data d : listing.getDefinedData(range, true)) {
				boolean past = d.getMaxAddress().compareTo(end) > 0;
				if (counted && (string(d) || integerArray(d))) {
					carved.add(d);
					continue;
				}
				boolean element = d.getDataType().isEquivalent(type) &&
					d.getAddress().subtract(start) % type.getLength() == 0;
				if (past || !element && !E200Types.primitive(d.getDataType())) {
					return null;
				}
			}
			return carved;
		}

		private static boolean string(Data d) {
			return d.getDataType() instanceof AbstractStringDataType;
		}

		/** Whether data is an array of integers or of undefined values */
		private static boolean integerArray(Data d) {
			return d.getDataType() instanceof Array a &&
				(E200Types.integer(a.getDataType()) || Undefined.isUndefined(a.getDataType()));
		}

		/**
		 * The parts of the carved arrays before and after the range, as arrays of their
		 * element type again (whole elements; the rest stays undefined)
		 */
		private static List<Remainder> remainders(List<Data> carved, Address start,
				Address end) {
			List<Remainder> remainders = new ArrayList<>();
			for (Data d : carved) {
				if (!(d.getDataType() instanceof Array a)) {
					continue; // a string: cleared
				}
				DataType element = a.getDataType();
				if (d.getAddress().compareTo(start) < 0) {
					long bytes = start.subtract(d.getAddress());
					remainders.add(new Remainder(d.getAddress(), element, (int) (bytes / element.getLength())));
				}
				if (d.getMaxAddress().compareTo(end) > 0) {
					long bytes = d.getMaxAddress().subtract(end);
					remainders.add(new Remainder(end.next(), element, (int) (bytes / element.getLength())));
				}
			}
			return remainders;
		}
	}

	/** An array to create again: a part of a carved array */
	private record Remainder(Address start, DataType element, int count) {
		void create(Listing listing, DataTypeManager manager) {
			if (count < 1 || start == null) {
				return;
			}
			try {
				listing.createData(start,
					new ArrayDataType(element, count, element.getLength(), manager));
			}
			catch (CodeUnitInsertionException e) {
				// the part stays undefined
			}
		}
	}

	/**
	 * The addresses that bound an array: those that pointers in memory point to, that code
	 * references, and that hold data or code that is not stray
	 */
	private static final class Boundaries {
		private final Program program;
		private final Listing listing;
		private final ReferenceManager references;
		/** The pointer targets, and the words that point to each */
		private final TreeMap<Address, List<Address>> pointers;

		Boundaries(Program program) {
			this.program = program;
			this.listing = program.getListing();
			this.references = program.getReferenceManager();
			this.pointers = new TreeMap<>(E200Data.pointerSources(program));
		}

		/**
		 * Whether an array a count field gives the length of may reach {@code end} past the
		 * limit: no code that is not stray lies in the range, and no instruction references
		 * an address in it that a word outside the array holds. The code's count says what
		 * the array covers; a word elsewhere that holds an address in it is a value that
		 * happens to be an address, a table of the flash sectors, or a word of code that
		 * was not disassembled, unless code uses the address.
		 */
		boolean passable(Address start, Address end, MemoryBlock block) {
			if (codeAfter(start, end.next(), block) != null) {
				return false;
			}
			for (Map.Entry<Address, List<Address>> e : pointers.subMap(start, false, end, true)
					.entrySet()) {
				boolean inside = true;
				for (Address source : e.getValue()) {
					inside &= source.compareTo(start) >= 0 && source.compareTo(end) <= 0;
				}
				if (!inside && referencedByCode(e.getKey())) {
					return false;
				}
			}
			return true;
		}

		/** Whether an instruction references an address */
		private boolean referencedByCode(Address address) {
			for (Reference ref : references.getReferencesTo(address)) {
				if (listing.getInstructionAt(ref.getFromAddress()) != null) {
					return true;
				}
			}
			return false;
		}

		/**
		 * The bytes from an address to the next boundary after it, or to the end of its
		 * block: the gap, and the limit an array may reach (the next pointer target, code, or
		 * data that is no single value)
		 */
		long[] bounds(Address address, MemoryBlock block) {
			Address limit = pointers.higherKey(address);
			Address code = codeAfter(address, limit, block);
			if (code != null) {
				limit = code;
			}
			Address next = limit;
			for (Data data = listing.getDefinedDataAfter(address); data != null &&
				before(data.getAddress(), limit); data = listing.getDefinedDataAfter(
					data.getMaxAddress())) {
				if (before(data.getAddress(), next)) {
					next = data.getAddress();
				}
				if (!E200Types.primitive(data.getDataType())) {
					limit = data.getAddress();
					break;
				}
			}
			Address from = address.next();
			if (from != null && from.compareTo(block.getEnd()) <= 0) {
				Address to = next == null || next.compareTo(block.getEnd()) > 0 ? block.getEnd()
						: next;
				AddressIterator it =
					references.getReferenceDestinationIterator(new AddressSet(from, to), true);
				if (it.hasNext()) {
					Address referenced = it.next();
					if (before(referenced, next)) {
						next = referenced;
					}
				}
			}
			return new long[] { bytesTo(next, address, block), bytesTo(limit, address, block) };
		}

		/**
		 * The first instruction after an address that is not stray, before {@code limit} and
		 * within the longest array; null if there is none
		 */
		private Address codeAfter(Address address, Address limit, MemoryBlock block) {
			Address reach;
			try {
				reach = address.addNoWrap(MAX_BYTES);
			}
			catch (AddressOverflowException e) {
				reach = block.getEnd();
			}
			if (before(reach, limit)) {
				limit = reach;
			}
			for (Instruction i = listing.getInstructionAfter(address); i != null &&
				before(i.getAddress(), limit); i = listing.getInstructionAfter(i.getAddress())) {
				if (!E200Data.stray(program, i)) {
					return i.getAddress();
				}
			}
			return null;
		}

		private static boolean before(Address a, Address b) {
			return a != null && (b == null || a.compareTo(b) < 0);
		}

		private static long bytesTo(Address next, Address address, MemoryBlock block) {
			if (next == null || next.compareTo(block.getEnd()) > 0) {
				return block.getEnd().subtract(address) + 1;
			}
			return next.subtract(address);
		}
	}
}
