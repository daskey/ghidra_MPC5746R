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
import ghidra.program.model.mem.*;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

/**
 * Operations on the data of the listing (shared by the steps of {@link E200Analyzer}):
 * replacing data by data of another type, labels, the structures at data that code passes by
 * address, and the data that pointers point to.
 */
final class E200Data {

	/** Pointers in one piece of data whose targets are typed */
	private static final int MAX_POINTERS = 4096;

	private E200Data() {
	}

	/**
	 * Replaces the data at an address by data of a type of the same length; returns whether
	 * it did. If the new data cannot be created, the old data is restored.
	 */
	static boolean replace(Listing listing, Address address, DataType type) {
		Data data = listing.getDefinedDataAt(address);
		if (data == null || data.getLength() != type.getLength()) {
			return false;
		}
		DataType old = data.getDataType();
		try {
			listing.clearCodeUnits(address, data.getMaxAddress(), false);
			listing.createData(address, type);
			return true;
		}
		catch (CodeUnitInsertionException e) {
			try {
				listing.createData(address, old);
			}
			catch (CodeUnitInsertionException e2) {
				// the old data could not be restored either; the bytes stay undefined
			}
			return false;
		}
	}

	/** Labels an address, unless it has a label already that is not the default one */
	static void label(Program program, Address address, String name, SourceType source) {
		SymbolTable symbols = program.getSymbolTable();
		Symbol primary = symbols.getPrimarySymbol(address);
		if (primary != null && primary.getSource() != SourceType.DEFAULT) {
			return;
		}
		try {
			symbols.createLabel(address, name, source);
		}
		catch (InvalidInputException e) {
			// not a valid name
		}
	}

	private static final Pattern EXTENSION = Pattern.compile(
		"followed by (\\S+) where f([0-9a-f]+) (=|!=) ([0-9a-f]+(?:, [0-9a-f]+)*)");

	/**
	 * The description of a structure whose instances are followed by the structure
	 * {@code extension} where {@code rule} holds (see {@link E200Structures#extension})
	 */
	static String extensionRule(String extension, String rule) {
		return "followed by " + extension + " where " + rule;
	}

	/**
	 * The structure that follows the instance of a structure at an address, or null: the
	 * structure's description names it and the values of a field that the instances it
	 * follows have ({@code followed by P_x_ext where f10 != 0}), and the bytes at the address
	 * hold such a value.
	 */
	static Structure extension(Program program, Address address, Structure s) {
		String description = s.getDescription();
		Matcher m = description == null ? null : EXTENSION.matcher(description);
		if (m == null || !m.find()) {
			return null;
		}
		DataType t = program.getDataTypeManager().getDataType(E200Types.CATEGORY, m.group(1));
		int offset = Integer.parseInt(m.group(2), 16);
		DataTypeComponent c = s.getComponentAt(offset);
		Memory memory = program.getMemory();
		MemoryBlock block = memory.getBlock(address);
		if (!(t instanceof Structure extension) || c == null || c.getOffset() != offset ||
			block == null || !block.isInitialized()) {
			return null;
		}
		long value;
		try {
			Address at = address.addNoWrap(offset);
			value = switch (c.getLength()) {
				case 1 -> memory.getByte(at) & 0xffL;
				case 2 -> memory.getShort(at) & 0xffffL;
				case 4 -> memory.getInt(at) & 0xffffffffL;
				default -> -1;
			};
		}
		catch (AddressOverflowException | MemoryAccessException e) {
			return null;
		}
		boolean listed = false;
		for (String v : m.group(4).split(", ")) {
			listed |= Long.parseLong(v, 16) == value;
		}
		return value >= 0 && m.group(3).equals("=") == listed ? extension : null;
	}

	/**
	 * Gives the data at an address that code passes as a pointer to a structure that
	 * structure, where there are only single values there, at fields of their size, pointers
	 * to nothing in particular that the reference analysis guessed, or structures of the
	 * analyzer's that lie inside it (the larger structure wins, whichever is applied first);
	 * returns whether it did. The data its pointer fields point to gets the pointed-to type
	 * (see {@link #targets}). Where the structure's instances with the bytes there are
	 * followed by fields of their own (see {@link #extension}), as the scale and offset of an
	 * integer-valued map, those get their structure too, on the same conditions, unless code
	 * passes their address, which starts another object.
	 */
	static boolean structureAt(Program program, Address address, Structure s) {
		boolean placed = place(program, address, s);
		Data data = program.getListing().getDefinedDataAt(address);
		Structure extension = data != null &&
			data.getDataType().getPathName().equals(s.getPathName())
					? extension(program, address, s)
					: null;
		if (extension != null) {
			Address after = address.add(s.getLength());
			if (program.getReferenceManager().getReferenceCountTo(after) == 0) {
				place(program, after, extension);
			}
		}
		return placed;
	}

	private static boolean place(Program program, Address address, Structure s) {
		Listing listing = program.getListing();
		MemoryBlock block = program.getMemory().getBlock(address);
		if (block == null || block.isVolatile() ||
			program.getFunctionManager().getFunctionContaining(address) != null) {
			return false;
		}
		Address end;
		try {
			end = address.addNoWrap(s.getLength() - 1);
		}
		catch (AddressOverflowException e) {
			return false;
		}
		Data at = listing.getDataContaining(address);
		if (!block.contains(end) || at != null && (!at.getAddress().equals(address) ||
			!E200Types.primitive(at.getDataType()) && !primitiveArray(at.getDataType()) &&
				!smallerStructure(at, s))) {
			return false;
		}
		AddressSet range = new AddressSet(address, end);
		if (!strayCode(program, range) ||
			block.isInitialized() && passedInside(program, address, end)) {
			return false;
		}
		for (Data d : listing.getDefinedData(range, true)) {
			DataType t = d.getDataType();
			if (d.getMaxAddress().compareTo(end) > 0) {
				return false;
			}
			if (smallerStructure(d, s)) {
				continue; // a structure of the analyzer's inside this one: the larger wins
			}
			if (t instanceof Pointer p && !E200Types.informative(p)) {
				continue; // a guess of the reference analysis at a value that is an address
			}
			// an array of single values is its elements; one of integers is what a copy loop
			// made of the structure, and says nothing about its fields
			int elements = primitiveArray(t) ? ((Array) t).getNumElements() : 1;
			DataType element = primitiveArray(t) ? ((Array) t).getDataType() : t;
			if (!E200Types.primitive(element)) {
				return false;
			}
			if (elements > 1 && (E200Types.integer(element) || Undefined.isUndefined(element))) {
				continue;
			}
			for (int i = 0; i < elements; i++) {
				int offset = (int) d.getAddress().subtract(address) + i * element.getLength();
				if (!valueAtField(s, offset, element)) {
					return false; // a value that is not a field, nor bytes of integer fields
				}
			}
		}
		try {
			listing.clearCodeUnits(address, end, false);
			listing.createData(address, s);
		}
		catch (CodeUnitInsertionException e) {
			return false;
		}
		targets(program, listing.getDataAt(address), 0);
		return true;
	}

	/**
	 * Whether code passes an address after {@code address} and up to {@code end} as a pointer:
	 * in flash (initialized bytes), another object starts there, as the next descriptor does
	 * where a lookup's structure holds the fields of a longer variant of the descriptor (in
	 * RAM, code passes the fields of a module's state by address)
	 */
	private static boolean passedInside(Program program, Address address, Address end) {
		Address from = address.next();
		if (from == null || from.compareTo(end) > 0) {
			return false;
		}
		ReferenceManager references = program.getReferenceManager();
		AddressIterator inside =
			references.getReferenceDestinationIterator(new AddressSet(from, end), true);
		while (inside.hasNext()) {
			for (Reference ref : references.getReferencesTo(inside.next())) {
				if (ref.getReferenceType() == RefType.PARAM) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Whether a single value of {@code type} at {@code offset} of a structure lies at a field
	 * of its size, an integer field it is the first bytes of, or whole integer fields
	 */
	private static boolean valueAtField(Structure s, int offset, DataType type) {
		if (Undefined.isUndefined(type) || integerOverFields(s, offset, type.getLength(), type)) {
			return true;
		}
		DataTypeComponent c = s.getComponentAt(offset);
		if (c == null || c.getDataType() instanceof DefaultDataType) {
			return false;
		}
		return c.getLength() == type.getLength() || c.getLength() > type.getLength() &&
			E200Types.integer(c.getDataType()) && E200Types.integer(type);
	}

	/** Whether a type is an array of single values */
	private static boolean primitiveArray(DataType type) {
		return type instanceof Array a && E200Types.primitive(a.getDataType());
	}

	/** Whether data is a structure of the analyzer's shorter than {@code s} */
	private static boolean smallerStructure(Data d, Structure s) {
		return E200Types.ownStructure(d.getDataType()) && d.getLength() < s.getLength();
	}

	/**
	 * Whether the code in a range, if any, is stray: instructions of no function that
	 * nothing flows to, as of data that was disassembled, which data may replace
	 */
	static boolean strayCode(Program program, AddressSetView range) {
		for (Instruction instruction : program.getListing().getInstructions(range, true)) {
			if (!stray(program, instruction)) {
				return false;
			}
		}
		return true;
	}

	/** How far a branch may lie from the instruction it flows to and be of its run */
	private static final int RUN_REACH = 32;
	/** How far the data around a run of stray instructions may lie for it to be cleared */
	private static final int DATA_REACH = 32;

	/**
	 * Whether an instruction is stray: of no function, and nothing flows to it but the
	 * instructions of its own run of instructions of no function, nearby, as data decoded to a
	 * branch to itself
	 */
	static boolean stray(Program program, Instruction instruction) {
		Address address = instruction.getAddress();
		Listing listing = program.getListing();
		if (listing.getFunctionContaining(address) != null) {
			return false;
		}
		for (Reference ref : program.getReferenceManager().getReferencesTo(address)) {
			if (ref.getReferenceType().isFlow() &&
				!sameRun(listing, ref.getFromAddress(), instruction)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Whether an address lies in the run of instructions of no function that an instruction
	 * is in, within {@link #RUN_REACH} bytes of it
	 */
	private static boolean sameRun(Listing listing, Address from, Instruction instruction) {
		Address a = instruction.getAddress();
		if (!from.getAddressSpace().equals(a.getAddressSpace()) ||
			Math.abs(from.subtract(a)) > RUN_REACH) {
			return false;
		}
		Address lo = from.compareTo(a) < 0 ? from : a;
		Address hi = from.compareTo(a) < 0 ? a : from;
		for (Address p = lo; p != null && p.compareTo(hi) <= 0;) {
			Instruction i = listing.getInstructionContaining(p);
			if (i == null || listing.getFunctionContaining(p) != null) {
				return false;
			}
			p = i.getMaxAddress().next();
		}
		return true;
	}

	/**
	 * Clears the runs of stray instructions (see {@link #stray}) that lie between data, with
	 * no symbol of the user's or of analysis: calibration data that the reference analysis
	 * disassembled, as the addresses that instructions form and the pointers in tables lead
	 * it to bytes that decode as code (all of a flash image is executable), where no data was
	 * placed over it. Runs next to code, as the targets of computed branches and the
	 * functions whose address code takes, stay. The "Found Code" bookmarks where data
	 * replaced such code go too. Returns how many instructions were cleared.
	 */
	static int clearStrayCode(Program program, TaskMonitor monitor) throws CancelledException {
		Listing listing = program.getListing();
		SymbolTable symbols = program.getSymbolTable();
		List<AddressRange> runs = new ArrayList<>();
		Address start = null;
		Address end = null;
		boolean clearable = true;
		for (Instruction i : listing.getInstructions(true)) {
			monitor.checkCancelled();
			boolean loose = listing.getFunctionContaining(i.getAddress()) == null;
			if (start != null && (!loose || !i.getAddress().equals(end.next()))) {
				if (clearable) {
					runs.add(new AddressRangeImpl(start, end));
				}
				start = null;
			}
			if (!loose) {
				continue;
			}
			if (start == null) {
				start = i.getAddress();
				clearable = true;
			}
			end = i.getMaxAddress();
			Symbol primary = symbols.getPrimarySymbol(i.getAddress());
			clearable &= (primary == null || primary.getSource() == SourceType.DEFAULT) &&
				!symbols.isExternalEntryPoint(i.getAddress()) && stray(program, i);
		}
		if (start != null && clearable) {
			runs.add(new AddressRangeImpl(start, end));
		}
		int cleared = 0;
		for (AddressRange run : runs) {
			monitor.checkCancelled();
			CodeUnit before = listing.getDefinedCodeUnitBefore(run.getMinAddress());
			CodeUnit after = listing.getDefinedCodeUnitAfter(run.getMaxAddress());
			if (!(before instanceof Data) || !(after instanceof Data) ||
				run.getMinAddress().subtract(before.getMaxAddress()) > DATA_REACH ||
				after.getMinAddress().subtract(run.getMaxAddress()) > DATA_REACH) {
				continue;
			}
			for (InstructionIterator i = listing.getInstructions(new AddressSet(run), true); i
					.hasNext(); i.next()) {
				cleared++;
			}
			listing.clearCodeUnits(run.getMinAddress(), run.getMaxAddress(), false);
		}
		BookmarkManager bookmarks = program.getBookmarkManager();
		List<Bookmark> stale = new ArrayList<>();
		Iterator<Bookmark> it = bookmarks.getBookmarksIterator(BookmarkType.ANALYSIS);
		while (it.hasNext()) {
			Bookmark b = it.next();
			if ("Found Code".equals(b.getCategory()) &&
				listing.getInstructionAt(b.getAddress()) == null &&
				listing.getDefinedDataContaining(b.getAddress()) != null) {
				stale.add(b);
			}
		}
		stale.forEach(bookmarks::removeBookmark);
		return cleared;
	}

	/**
	 * Whether an integer of {@code length} bytes at {@code offset} in a structure covers whole
	 * fields that are integers or undefined, as a halfword that code writes over a byte and
	 * its complement does
	 */
	private static boolean integerOverFields(Structure s, int offset, int length, DataType t) {
		if (!E200Types.integer(t) || offset + length > s.getLength()) {
			return false;
		}
		DataTypeComponent first = s.getComponentAt(offset);
		if (first == null || first.getOffset() != offset) {
			return false;
		}
		for (DataTypeComponent c : s.getComponents()) {
			if (c.getOffset() >= offset && c.getOffset() < offset + length) {
				DataType ct = c.getDataType();
				if (c.getOffset() + c.getLength() > offset + length ||
					!(Undefined.isUndefined(ct) || E200Types.integer(ct))) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Creates data of the pointed-to type where the pointers in new data, its fields and
	 * elements included, point to nothing defined yet, and so on for pointers in that data. In
	 * a flash image all of flash is executable, and the reference analysis would take an
	 * undefined target for code and disassemble it, or for a pointer if its value is an
	 * address, as a float 2.0 (0x40000000, the start of SRAM) is.
	 */
	static void targets(Program program, Data data, int depth) {
		if (data == null || depth > 3) {
			return;
		}
		Listing listing = program.getListing();
		List<Data> fields = new ArrayList<>();
		pointersIn(data, fields, 0);
		for (Data field : fields) {
			if (!(field.getDataType() instanceof Pointer pointer) ||
				!(field.getValue() instanceof Address target)) {
				continue;
			}
			DataType type = pointer.getDataType();
			if (type instanceof VoidDataType) {
				type = ByteDataType.dataType; // what is there is not known, but not code
			}
			MemoryBlock block = program.getMemory().getBlock(target);
			if (type == null || type.getLength() <= 0 || block == null ||
				!block.isInitialized()) {
				continue;
			}
			if (E200Types.ownStructure(type)) {
				// over single values at its fields too, as a descriptor whose count field
				// code reads directly
				structureAt(program, target, (Structure) type);
				continue;
			}
			try {
				Address end = target.addNoWrap(type.getLength() - 1);
				if (!block.contains(end)) {
					continue;
				}
				if (!listing.isUndefined(target, end) && untypedAt(program, target, end, type)) {
					listing.clearCodeUnits(target, end, false);
				}
				if (listing.isUndefined(target, end)) {
					targets(program, listing.createData(target, type), depth + 1);
				}
			}
			catch (AddressOverflowException | CodeUnitInsertionException e) {
				// no room for the target
			}
		}
	}

	/**
	 * Whether there is only untyped data where a pointer to {@code type} points: undefined
	 * values, or pointers to nothing in particular, which the reference analysis makes of
	 * values that are addresses, as the float 2.0 (0x40000000) is, and of the pointer fields
	 * of a structure
	 */
	private static boolean untypedAt(Program program, Address target, Address end,
			DataType type) {
		Listing listing = program.getListing();
		if (!E200Types.informative(type) || !strayCode(program, new AddressSet(target, end))) {
			return false;
		}
		Data first = listing.getDataContaining(target);
		if (first != null && !first.getAddress().equals(target)) {
			return false;
		}
		for (Data d : listing.getDefinedData(new AddressSet(target, end), true)) {
			DataType t = d.getDataType();
			boolean guessed = t instanceof Pointer p && !E200Types.informative(p);
			if (d.getMaxAddress().compareTo(end) > 0 || !Undefined.isUndefined(t) && !guessed) {
				return false;
			}
		}
		return true;
	}

	/**
	 * The addresses that aligned words of initialized memory hold, outside code: pointers to
	 * data that code may only reach through them
	 */
	static Set<Address> pointerTargets(Program program) {
		return pointerSources(program).keySet();
	}

	/**
	 * The addresses that aligned words of initialized memory hold, outside code, and the
	 * addresses of the words that hold each: a word in an array of values that happens to be
	 * an address is no pointer
	 */
	static Map<Address, List<Address>> pointerSources(Program program) {
		Map<Address, List<Address>> targets = new HashMap<>();
		Memory memory = program.getMemory();
		Listing listing = program.getListing();
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
				Address source = block.getStart().add(i);
				if (memory.contains(target) && listing.getInstructionContaining(source) == null) {
					targets.computeIfAbsent(target, t -> new ArrayList<>(1)).add(source);
				}
			}
		}
		return targets;
	}

	/** Pointers in data: the data itself, or its components and theirs, as in a table */
	private static void pointersIn(Data data, List<Data> pointers, int level) {
		if (data == null || pointers.size() >= MAX_POINTERS) {
			return;
		}
		if (data.getDataType() instanceof Pointer) {
			pointers.add(data);
			return;
		}
		for (int i = 0; level < 3 && i < data.getNumComponents(); i++) {
			pointersIn(data.getComponent(i), pointers, level + 1);
		}
	}
}
