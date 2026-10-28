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

import java.math.BigInteger;
import java.util.*;

import ghidra.app.util.PseudoDisassembler;
import ghidra.app.util.PseudoInstruction;
import ghidra.framework.options.Options;
import ghidra.program.model.address.*;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.*;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.PropertyMapManager;
import ghidra.program.model.util.StringPropertyMap;
import ghidra.util.Msg;
import ghidra.util.exception.*;
import ghidra.util.task.TaskMonitor;

/**
 * The small data area bases of the PowerPC EABI (part of {@link E200Analyzer}): r13
 * ({@code _SDA_BASE_}) and r2 ({@code _SDA2_BASE_}) hold one value in all the code of a
 * program, so that {@code e_lwz r3,-0x7ff0(r13)} accesses a global. The values come from the
 * linker symbols or from the startup code that loads the registers, found by its bytes even
 * where analysis does not reach it. When startup code loads different values, as in an image
 * with a bootloader and an application, each value applies to the code its startup code
 * reaches, up to the erased flash before the next program, and code copied to local memory
 * gets the values of the program it was copied from.
 * <p>
 * The values are worked out at every analysis, not only the first: the analyzer records the
 * values it sets in the program, and replaces them where the symbols, the startup code or the
 * memory changed, or where they were removed. Values that something else set, the loader or
 * the user, or that the user changed, are left alone; a value the evidence gives counts as
 * the analyzer's, as one an analysis set before the values were recorded. {@link #update}
 * returns where values changed and from what, for the analyzer to remove the references made
 * with the earlier values and to propagate constants there again.
 */
final class E200SmallDataBases {

	private static final String OPTION_NAME = "Assume small data area bases";
	private static final String OPTION_DESCRIPTION =
		"Assume the EABI small data area base registers r13 (_SDA_BASE_) and r2\n" +
			"(_SDA2_BASE_) in executable memory, at every analysis. The values come from the\n" +
			"_SDA_BASE_ and _SDA2_BASE_ symbols or from the startup code that loads the\n" +
			"registers. When startup code loads different values, as in an image with a\n" +
			"bootloader and an application, each value applies to the program that loads it.\n" +
			"Values set otherwise, by the loader or the user, are left alone.";

	/** Small data area base registers and the linker symbols that define them. */
	private static final String[][] BASES = { { "r13", "_SDA_BASE_" }, { "r2", "_SDA2_BASE_" } };

	/** Property map of the values the analyzer set: range start to "end value" in hex */
	private static final String RECORD = E200Analyzer.NAME + " assumed ";

	/** Instructions after the e_lis in which startup code adds the lower half */
	private static final int STARTUP_SEARCH_INSTRUCTIONS = 4;

	/** Instructions that complete an address loaded with e_lis: operand holding the low half. */
	private static final Map<String, Integer> LOW_HALF_OPERAND =
		Map.of("e_add16i", 2, "e_addi", 2, "e_or2i", 1, "e_add2i.", 1);

	/** Bound on the code traced from each startup load. */
	private static final int MAX_REACHED_INSTRUCTIONS = 500_000;

	/** Shortest run of erased flash taken as the boundary between two programs. */
	private static final int MIN_ERASED_RUN = 16;

	/** Samples of a block searched for in the programs to find which one it copies. */
	private static final int COPY_SAMPLES = 8;
	private static final int COPY_SAMPLE_SIZE = 32;
	private static final int COPY_SAMPLE_DISTINCT = 8;

	private boolean enabled = true;

	/**
	 * Where each value goes for a register, from what evidence: the last one worked out, kept
	 * so that an analysis of unchanged evidence does not trace the startup code again
	 */
	private record Assignment(AddressSetView code, Long symbol,
			SortedMap<Long, List<Address>> loads, Map<Long, AddressSet> regions) {

		String source(long value) {
			return symbol != null ? "the symbol" : "startup code at " + loads.get(value);
		}

		/** The values the evidence gives */
		Set<Long> values() {
			return symbol != null ? Set.of(symbol) : loads.keySet();
		}
	}

	private final Map<String, Assignment> assignments = new HashMap<>();

	void registerOptions(Options options) {
		options.registerOption(OPTION_NAME, enabled, null, OPTION_DESCRIPTION);
	}

	void optionsChanged(Options options) {
		enabled = options.getBoolean(OPTION_NAME, enabled);
	}

	/** A range where a register's value changed, from {@code before} to {@code after} */
	record Change(Register register, AddressRange range, BigInteger before, BigInteger after) {}

	/**
	 * Sets the small data area bases where the evidence puts them, replacing the values this
	 * analyzer set before where it changed.
	 *
	 * @return where values changed, and from what to what (null for no value)
	 */
	List<Change> update(Program program, TaskMonitor monitor) throws CancelledException {
		List<Change> changes = new ArrayList<>();
		if (!enabled) {
			return changes;
		}
		AddressSetView code = E200Code.executableMemory(program);
		for (String[] base : BASES) {
			monitor.checkCancelled();
			Register reg = program.getRegister(base[0]);
			if (reg != null) {
				Assignment assignment = assignment(program, reg, base[1], code, monitor);
				changes.addAll(apply(program, reg, assignment, monitor));
			}
		}
		return changes;
	}

	/** Where the values of a register go, worked out again only if the evidence changed */
	private Assignment assignment(Program program, Register reg, String symbolName,
			AddressSetView code, TaskMonitor monitor) throws CancelledException {
		Long symbol = symbolValue(program, symbolName);
		SortedMap<Long, List<Address>> loads =
			symbol != null ? new TreeMap<>() : findStartupLoads(program, reg, monitor);
		Assignment last = assignments.get(reg.getName());
		if (last != null && last.code().hasSameAddresses(code) &&
			Objects.equals(last.symbol(), symbol) &&
			last.loads().equals(loads)) {
			return last;
		}
		Map<Long, AddressSet> regions = new HashMap<>();
		if (symbol != null) {
			regions.put(symbol, new AddressSet(code));
		}
		else if (loads.size() == 1) {
			regions.put(loads.firstKey(), new AddressSet(code));
		}
		else if (loads.size() > 1) {
			regions = perProgram(program, loads, code, monitor);
		}
		Assignment assignment = new Assignment(code, symbol, loads, regions);
		assignments.put(reg.getName(), assignment);
		return assignment;
	}

	/**
	 * Gives the register the assigned values where it has no value or one this analyzer set,
	 * and removes the values this analyzer set that the assignment no longer has; records
	 * what it set. Returns where values changed.
	 */
	private static List<Change> apply(Program program, Register reg, Assignment assignment,
			TaskMonitor monitor) throws CancelledException {
		ProgramContext context = program.getProgramContext();
		StringPropertyMap record = record(program, reg);
		// the values set now, and those of them this analyzer set
		Map<BigInteger, AddressSet> current = new HashMap<>();
		AddressRangeIterator ranges = context.getRegisterValueAddressRanges(reg);
		while (ranges.hasNext()) {
			AddressRange range = ranges.next();
			BigInteger value = context.getValue(reg, range.getMinAddress(), false);
			if (value != null) {
				current.computeIfAbsent(value, v -> new AddressSet()).add(range);
			}
		}
		// those it recorded, still as it set them, and in executable memory any of the values
		// the evidence gives, as set by an analysis before the values were recorded
		Map<BigInteger, AddressSet> own = new HashMap<>();
		for (Long value : assignment.values()) {
			BigInteger v = unsigned(value);
			if (current.containsKey(v)) {
				own.computeIfAbsent(v, x -> new AddressSet())
						.add(current.get(v).intersect(assignment.code()));
			}
		}
		AddressIterator starts = record.getPropertyIterator();
		while (starts.hasNext()) {
			monitor.checkCancelled();
			Address start = starts.next();
			String[] entry = record.getString(start).split(" ");
			Address end = start.getNewAddress(Long.parseUnsignedLong(entry[0], 16));
			BigInteger value = new BigInteger(entry[1], 16);
			AddressSet intact = new AddressSet(start, end)
					.intersect(current.getOrDefault(value, new AddressSet()));
			own.computeIfAbsent(value, v -> new AddressSet()).add(intact);
		}
		AddressSet foreign = new AddressSet();
		current.values().forEach(foreign::add);
		own.values().forEach(foreign::delete);

		AddressSet changed = new AddressSet();
		Map<BigInteger, AddressSet> wanted = new HashMap<>();
		for (Map.Entry<Long, AddressSet> e : assignment.regions().entrySet()) {
			wanted.put(unsigned(e.getKey()), e.getValue().subtract(foreign));
		}
		for (Map.Entry<BigInteger, AddressSet> e : own.entrySet()) {
			AddressSet stale = e.getValue().subtract(wanted.getOrDefault(e.getKey(),
				new AddressSet()));
			for (AddressRange range : stale) {
				remove(context, reg, range);
			}
			changed.add(stale);
			if (!stale.isEmpty()) {
				Msg.info(E200Analyzer.class, "No longer assuming " + reg + " = 0x" +
					e.getKey().toString(16) + " in " + describe(stale));
			}
		}
		for (Map.Entry<BigInteger, AddressSet> e : wanted.entrySet()) {
			AddressSet set = e.getValue().subtract(own.getOrDefault(e.getKey(), new AddressSet()));
			if (set.isEmpty()) {
				continue;
			}
			for (AddressRange range : set) {
				setValue(context, reg, range, e.getKey());
			}
			changed.add(set);
			Msg.info(E200Analyzer.class, "Assuming " + reg + " = 0x" + e.getKey().toString(16) +
				" (" + assignment.source(e.getKey().longValue()) + ") in " +
				(set.hasSameAddresses(assignment.code()) ? "all executable memory"
						: describe(set)));
		}
		Map<Address, String> entries = new HashMap<>();
		for (Map.Entry<BigInteger, AddressSet> e : wanted.entrySet()) {
			for (AddressRange range : e.getValue()) {
				entries.put(range.getMinAddress(), Long.toHexString(range.getMaxAddress()
						.getOffset()) + " " + e.getKey().toString(16));
			}
		}
		if (!entries.equals(recorded(record))) {
			record.clear();
			entries.forEach(record::add);
		}
		return changes(context, reg, changed, current);
	}

	/** The changes in {@code changed}, split where the values before and after change */
	private static List<Change> changes(ProgramContext context, Register reg,
			AddressSetView changed, Map<BigInteger, AddressSet> before) {
		List<Change> changes = new ArrayList<>();
		AddressSet unset = new AddressSet(changed);
		for (Map.Entry<BigInteger, AddressSet> e : before.entrySet()) {
			AddressSet part = e.getValue().intersect(changed);
			unset.delete(part);
			for (AddressRange range : part) {
				changes.addAll(changes(context, reg, range, e.getKey()));
			}
		}
		for (AddressRange range : unset) {
			changes.addAll(changes(context, reg, range, null));
		}
		return changes;
	}

	/** The changes in a range that had one value before, split by the values after */
	private static List<Change> changes(ProgramContext context, Register reg, AddressRange range,
			BigInteger before) {
		List<Change> changes = new ArrayList<>();
		AddressSet unset = new AddressSet(range);
		AddressRangeIterator after = context.getRegisterValueAddressRanges(reg,
			range.getMinAddress(), range.getMaxAddress());
		while (after.hasNext()) {
			AddressRange r = after.next();
			unset.delete(r);
			BigInteger value = context.getValue(reg, r.getMinAddress(), false);
			changes.add(new Change(reg, r, before, value));
		}
		for (AddressRange r : unset) {
			changes.add(new Change(reg, r, before, null));
		}
		return changes;
	}

	private static Map<Address, String> recorded(StringPropertyMap record) {
		Map<Address, String> entries = new HashMap<>();
		AddressIterator it = record.getPropertyIterator();
		while (it.hasNext()) {
			Address a = it.next();
			entries.put(a, record.getString(a));
		}
		return entries;
	}

	private static BigInteger unsigned(long value) {
		return BigInteger.valueOf(value & 0xffffffffL);
	}

	/** The record of the values this analyzer set for a register */
	private static StringPropertyMap record(Program program, Register reg) {
		PropertyMapManager properties = program.getUsrPropertyManager();
		StringPropertyMap map = properties.getStringPropertyMap(RECORD + reg.getName());
		if (map == null) {
			try {
				map = properties.createStringPropertyMap(RECORD + reg.getName());
			}
			catch (DuplicateNameException e) {
				throw new AssertException(e); // checked above
			}
		}
		return map;
	}

	private static void setValue(ProgramContext context, Register reg, AddressRange range,
			BigInteger value) {
		try {
			context.setValue(reg, range.getMinAddress(), range.getMaxAddress(), value);
		}
		catch (ContextChangeException e) {
			throw new AssertException(e); // not a context register
		}
	}

	private static void remove(ProgramContext context, Register reg, AddressRange range) {
		try {
			context.remove(range.getMinAddress(), range.getMaxAddress(), reg);
		}
		catch (ContextChangeException e) {
			throw new AssertException(e); // not a context register
		}
	}

	/**
	 * The regions of the values of a register that different startup code loads differently,
	 * as in an image with several separately linked programs such as a boot manager, a
	 * bootloader and an application. Each value applies to the program whose startup code
	 * loads it: the span of the code that the startup code reaches, extended to the erased
	 * flash that separates it from the next program. Code between programs without erased
	 * flash gets no value. A block with code of no program, such as code copied to RAM, gets
	 * the values of the program whose code it copies.
	 */
	private static Map<Long, AddressSet> perProgram(Program program,
			SortedMap<Long, List<Address>> loads, AddressSetView code, TaskMonitor monitor)
			throws CancelledException {
		Set<Address> sites = new HashSet<>();
		loads.values().forEach(sites::addAll);

		// the code each value's startup code reaches, without the code reached with other values
		Map<Long, AddressSet> reached = new HashMap<>();
		PseudoDisassembler disassembler = new PseudoDisassembler(program);
		for (Map.Entry<Long, List<Address>> entry : loads.entrySet()) {
			AddressSet set = new AddressSet();
			for (Address site : entry.getValue()) {
				set.add(reachedCode(disassembler, site, sites, code, monitor));
			}
			reached.put(entry.getKey(), set);
		}
		Map<Long, AddressSet> own = new HashMap<>();
		for (Map.Entry<Long, AddressSet> entry : reached.entrySet()) {
			AddressSet set = new AddressSet(entry.getValue());
			for (Map.Entry<Long, AddressSet> other : reached.entrySet()) {
				if (!other.getKey().equals(entry.getKey())) {
					set.delete(other.getValue());
				}
			}
			own.put(entry.getKey(), set);
		}

		Map<Long, AddressSet> regions = partition(program, own, monitor);

		// blocks with code of no program, such as code copied to RAM: the values of the
		// program whose code they copy
		AddressSet covered = new AddressSet();
		regions.values().forEach(covered::add);
		for (MemoryBlock block : program.getMemory().getBlocks()) {
			if (code.contains(block.getStart(), block.getEnd()) &&
				!covered.intersects(block.getStart(), block.getEnd())) {
				Long owner = copiedFrom(program.getMemory(), block, regions, monitor);
				if (owner != null) {
					regions.get(owner).add(block.getStart(), block.getEnd());
				}
			}
		}
		for (AddressSet region : regions.values()) {
			region.delete(region.subtract(code));
		}
		return regions;
	}

	private static Long symbolValue(Program program, String name) {
		Symbol symbol = SymbolUtilities.getLabelOrFunctionSymbol(program, name,
			err -> Msg.info(E200Analyzer.class, err));
		return symbol == null ? null : symbol.getAddress().getOffset();
	}

	/**
	 * Divides memory between values, given the code that belongs to each: a value gets the
	 * addresses from its first to its last code in each memory block, where no other value's
	 * code lies between. Between the code of two different values, the longest run of erased
	 * bytes is the boundary; without one the addresses between get no value. Before the first
	 * and after the last code of a block, a value extends to the end of the block.
	 */
	private static Map<Long, AddressSet> partition(Program program, Map<Long, AddressSet> own,
			TaskMonitor monitor) throws CancelledException {
		record Span(Address start, Address end, long value) {}

		Map<Long, AddressSet> regions = new HashMap<>();
		Memory memory = program.getMemory();
		for (MemoryBlock block : memory.getBlocks()) {
			AddressSet blockSet = new AddressSet(block.getStart(), block.getEnd());
			// merge the ranges of the same value that follow each other
			List<Span> spans = new ArrayList<>();
			TreeMap<Address, Span> ranges = new TreeMap<>();
			for (Map.Entry<Long, AddressSet> entry : own.entrySet()) {
				for (AddressRange range : entry.getValue().intersect(blockSet)) {
					ranges.put(range.getMinAddress(),
						new Span(range.getMinAddress(), range.getMaxAddress(), entry.getKey()));
				}
			}
			for (Span span : ranges.values()) {
				Span last = spans.isEmpty() ? null : spans.get(spans.size() - 1);
				if (last != null && last.value() == span.value()) {
					spans.set(spans.size() - 1, new Span(last.start(), span.end(), span.value()));
				}
				else {
					spans.add(span);
				}
			}
			if (spans.isEmpty()) {
				continue;
			}
			Address start = block.getStart();
			for (int i = 0; i < spans.size(); i++) {
				monitor.checkCancelled();
				Span span = spans.get(i);
				Address end = block.getEnd();
				Address next = null;
				if (i + 1 < spans.size()) {
					AddressRange gap = new AddressRangeImpl(span.end(), spans.get(i + 1).start());
					AddressRange erased = longestErasedRun(memory, gap);
					if (erased != null) {
						end = erased.getMinAddress().previous();
						next = erased.getMaxAddress().next();
					}
					else {
						end = span.end();
						next = spans.get(i + 1).start();
					}
				}
				if (start != null && end != null && start.compareTo(end) <= 0) {
					regions.computeIfAbsent(span.value(), v -> new AddressSet()).add(start, end);
				}
				start = next;
			}
		}
		return regions;
	}

	/**
	 * The value of the program whose code a block copies: samples of the block's bytes are
	 * searched for in the regions of each value. Null if no sample is found, or samples are
	 * found in the regions of different values.
	 */
	private static Long copiedFrom(Memory memory, MemoryBlock block,
			Map<Long, AddressSet> regions, TaskMonitor monitor) throws CancelledException {
		Set<Long> owners = new HashSet<>();
		byte[] sample = new byte[COPY_SAMPLE_SIZE];
		for (int i = 0; i < COPY_SAMPLES; i++) {
			monitor.checkCancelled();
			long offset = (block.getSize() * i / COPY_SAMPLES) & ~1L;
			if (offset + sample.length > block.getSize()) {
				break;
			}
			try {
				if (memory.getBytes(block.getStart().add(offset), sample) != sample.length) {
					continue;
				}
			}
			catch (MemoryAccessException e) {
				continue;
			}
			Set<Byte> distinct = new HashSet<>();
			for (byte b : sample) {
				distinct.add(b);
			}
			if (distinct.size() < COPY_SAMPLE_DISTINCT) {
				continue; // erased, zeroed or repetitive bytes are found anywhere
			}
			for (Map.Entry<Long, AddressSet> entry : regions.entrySet()) {
				for (AddressRange range : entry.getValue()) {
					if (memory.findBytes(range.getMinAddress(), range.getMaxAddress(), sample,
						null, true, monitor) != null) {
						owners.add(entry.getKey());
						break;
					}
				}
			}
		}
		return owners.size() == 1 ? owners.iterator().next() : null;
	}

	/**
	 * Longest run of at least {@link #MIN_ERASED_RUN} erased (0xFF) bytes strictly inside
	 * {@code range}, or null if there is none.
	 */
	private static AddressRange longestErasedRun(Memory memory, AddressRange range) {
		Address first = range.getMinAddress().next();
		Address last = range.getMaxAddress().previous();
		if (first == null || last == null || first.compareTo(last) > 0) {
			return null;
		}
		byte[] bytes = new byte[0x10000];
		Address bestStart = null;
		long bestLength = MIN_ERASED_RUN - 1;
		Address runStart = null;
		long runLength = 0;
		Address address = first;
		while (address != null && address.compareTo(last) <= 0) {
			int len = (int) Math.min(bytes.length, last.subtract(address) + 1);
			int got;
			try {
				got = memory.getBytes(address, bytes, 0, len);
			}
			catch (MemoryAccessException e) {
				return null;
			}
			for (int i = 0; i < got; i++) {
				if (bytes[i] == (byte) 0xff) {
					if (runLength++ == 0) {
						runStart = address.add(i);
					}
					if (runLength > bestLength) {
						bestLength = runLength;
						bestStart = runStart;
					}
				}
				else {
					runLength = 0;
				}
			}
			if (got < len) {
				return null;
			}
			address = address.addWrap(got);
			if (address.compareTo(first) <= 0) {
				break; // wrapped
			}
		}
		return bestStart == null ? null
				: new AddressRangeImpl(bestStart, bestStart.add(bestLength - 1));
	}

	/**
	 * Code reached from {@code start} by following fallthroughs, branches and direct calls,
	 * stopping at other {@code sites} and at bytes that are not instructions.
	 */
	private static AddressSet reachedCode(PseudoDisassembler disassembler, Address start,
			Set<Address> sites, AddressSetView code, TaskMonitor monitor)
			throws CancelledException {
		AddressSet reached = new AddressSet();
		Deque<Address> todo = new ArrayDeque<>();
		todo.push(start);
		int count = 0;
		while (!todo.isEmpty() && count < MAX_REACHED_INSTRUCTIONS) {
			monitor.checkCancelled();
			Address at = todo.pop();
			while (at != null && code.contains(at) && !reached.contains(at) &&
				(at.equals(start) || !sites.contains(at))) {
				PseudoInstruction ins;
				try {
					ins = disassembler.disassemble(at);
				}
				catch (Exception e) {
					break;
				}
				if (ins == null || ins.getMnemonicString().equals("se_illegal")) {
					break; // not code, such as erased or zeroed flash
				}
				reached.add(ins.getMinAddress(), ins.getMaxAddress());
				if (++count >= MAX_REACHED_INSTRUCTIONS) {
					break;
				}
				for (Address target : ins.getFlows()) {
					todo.push(target);
				}
				at = ins.getFallThrough();
			}
		}
		return reached;
	}

	/**
	 * Finds the values that startup code loads into {@code reg} with {@code e_lis}, followed by
	 * an instruction that adds or ORs the low half, as in
	 * {@code e_lis r13,_SDA_BASE_@ha; e_add16i r13,r13,_SDA_BASE_@l}.
	 *
	 * @return the values found, with the addresses of the e_lis instructions
	 */
	private static SortedMap<Long, List<Address>> findStartupLoads(Program program, Register reg,
			TaskMonitor monitor) throws CancelledException {
		SortedMap<Long, List<Address>> loads = new TreeMap<>();
		int regNum = reg.getName().equals("r13") ? 13 : 2;
		// OP=28 (I16L form) and the register in the rD field
		int prefix = (28 << 5) | regNum;
		Memory memory = program.getMemory();
		Listing listing = program.getListing();
		PseudoDisassembler disassembler = new PseudoDisassembler(program);
		byte[] bytes = new byte[0x10000];
		for (AddressRange range : E200Code.executableMemory(program)) {
			Address address = range.getMinAddress();
			// instructions are halfword aligned
			if ((address.getOffset() & 1) != 0) {
				address = address.next();
			}
			while (address != null && range.contains(address)) {
				monitor.checkCancelled();
				long remaining = range.getMaxAddress().subtract(address) + 1;
				int len = (int) Math.min(bytes.length, remaining);
				int got;
				try {
					got = memory.getBytes(address, bytes, 0, len);
				}
				catch (MemoryAccessException e) {
					break;
				}
				for (int i = 0; i + 3 < got; i += 2) {
					int word = ((bytes[i] & 0xff) << 24) | ((bytes[i + 1] & 0xff) << 16) |
						((bytes[i + 2] & 0xff) << 8) | (bytes[i + 3] & 0xff);
					if ((word >>> 21) != prefix) {
						continue;
					}
					Address at = address.add(i);
					if (listing.getDefinedDataContaining(at) != null) {
						continue;
					}
					Long value = startupLoad(disassembler, at, reg);
					if (value != null && value != 0) {
						loads.computeIfAbsent(value, v -> new ArrayList<>()).add(at);
					}
				}
				if (got < 4 || remaining <= got) {
					break;
				}
				// overlap by one halfword so no instruction spans a buffer boundary unseen
				address = address.add((got - 2) & ~1);
			}
		}
		return loads;
	}

	/**
	 * Value loaded into {@code reg} by the e_lis at {@code at} and the instruction that adds
	 * or ORs the low half, if that follows within a few instructions.
	 */
	private static Long startupLoad(PseudoDisassembler disassembler, Address at, Register reg) {
		try {
			PseudoInstruction lis = disassembler.disassemble(at);
			if (!"e_lis".equals(lis.getMnemonicString()) || !reg.equals(lis.getRegister(0))) {
				return null;
			}
			Scalar high = lis.getScalar(1);
			if (high == null) {
				return null;
			}
			long value = high.getUnsignedValue() << 16;
			Address next = lis.getMaxAddress().next();
			for (int n = 0; n < STARTUP_SEARCH_INSTRUCTIONS && next != null; n++) {
				PseudoInstruction ins = disassembler.disassemble(next);
				String mnemonic = ins.getMnemonicString();
				Integer lowOperand = LOW_HALF_OPERAND.get(mnemonic);
				if (lowOperand != null && reg.equals(ins.getRegister(0))) {
					if (lowOperand == 2 && !reg.equals(ins.getRegister(1))) {
						return null;
					}
					Scalar low = ins.getScalar(lowOperand);
					if (low == null) {
						return null;
					}
					value = mnemonic.equals("e_or2i") ? value | low.getUnsignedValue()
							: value + low.getSignedValue();
					return value & 0xffffffffL;
				}
				if (E200Code.writes(ins, reg) || ins.getFlowType().isJump() ||
					ins.getFlowType().isTerminal()) {
					return null;
				}
				next = ins.getMaxAddress().next();
			}
		}
		catch (Exception e) {
			// not an instruction
		}
		return null;
	}

	private static String describe(AddressSetView set) {
		if (set.getNumAddressRanges() > 3) {
			return set.getNumAddressRanges() + " ranges from " + set.getMinAddress() + " to " +
				set.getMaxAddress();
		}
		StringJoiner joiner = new StringJoiner(", ");
		for (AddressRange range : set) {
			joiner.add(range.getMinAddress() + "-" + range.getMaxAddress());
		}
		return joiner.toString();
	}

}
