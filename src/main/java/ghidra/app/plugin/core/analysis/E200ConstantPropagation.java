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

import ghidra.app.cmd.function.CreateFunctionCmd;
import ghidra.app.cmd.label.AddLabelCmd;
import ghidra.app.plugin.core.disassembler.AddressTable;
import ghidra.app.util.PseudoDisassembler;
import ghidra.app.util.PseudoInstruction;
import ghidra.app.util.importer.MessageLog;
import ghidra.framework.options.Options;
import ghidra.program.model.address.*;
import ghidra.program.model.block.*;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.Undefined;
import ghidra.program.model.lang.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.*;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.program.util.*;
import ghidra.util.Msg;
import ghidra.util.exception.*;
import ghidra.util.task.TaskMonitor;

/**
 * Constant propagation for the NXP e200z4 VLE language ({@code PowerPC:BE:32:VLE-e200}), part
 * of {@link E200Analyzer}. It is derived from Ghidra's {@code PowerPCAddressAnalyzer}, which
 * the language's processor spec disables, and is not an analyzer of its own: Ghidra finds
 * analyzers by the end of their class names. Compared with that analyzer it:
 * <ul>
 * <li>assumes the EABI small data area bases in r13 ({@code _SDA_BASE_}) and r2
 * ({@code _SDA2_BASE_}) in all code, taken from existing register values, the symbols, or the
 * startup code that loads them, so that small data accesses resolve to addresses. In an image
 * with several programs, each program gets the values its own startup code loads.</li>
 * <li>recognizes VLE instructions: no references from {@code e_lis} (the upper half of an
 * address) or from {@code e_li}, {@code se_li}, {@code se_bgeni} and {@code se_bmaski}
 * constants, and switch table recovery at {@code se_bctr} with VLE compares as the guard</li>
 * <li>reads switch tables from writable memory when values from writable memory are trusted,
 * as for flash images loaded into a single read/write block</li>
 * <li>drops the PEF and ELF function descriptor (r2/r30) handling, which does not apply to
 * the e200 EABI</li>
 * </ul>
 */
final class E200ConstantPropagation extends ConstantPropagationAnalyzer {

	private static final String PROCESSOR_NAME = "PowerPC e200";

	private static final String OPTION_NAME_SDA = "Assume small data area bases";
	private static final String OPTION_DESCRIPTION_SDA =
		"Assume the EABI small data area base registers r13 (_SDA_BASE_) and r2 (_SDA2_BASE_)\n" +
			"in all executable memory, unless they already have values there. The values come\n" +
			"from the _SDA_BASE_ and _SDA2_BASE_ symbols or from the startup code that loads\n" +
			"the registers. When startup code loads different values, as in an image with a\n" +
			"bootloader and an application, each value applies to the program that loads it.";
	private static final boolean OPTION_DEFAULT_SDA = true;

	private static final String SWITCH_OPTION_NAME = "Switch Table Recovery";
	private static final String SWITCH_OPTION_DESCRIPTION = "Turn on to recover switch tables";
	private static final boolean SWITCH_OPTION_DEFAULT_VALUE = true;

	/** Instructions that only load a constant, never a complete address. */
	private static final Set<String> CONSTANT_LOADS =
		Set.of("e_li", "se_li", "li", "e_lis", "lis", "se_bgeni", "se_bmaski");

	/** Indirect branches through CTR that may be switches. */
	private static final Set<String> COMPUTED_JUMPS = Set.of("se_bctr", "bctr", "bcctr");

	/** Compares whose immediate bounds a switch index. */
	private static final Set<String> SWITCH_GUARDS = Set.of("e_cmpli", "e_cmpi", "e_cmpl16i",
		"e_cmp16i", "se_cmpli", "se_cmpi", "cmpli", "cmplwi", "cmpi", "cmpwi");

	/** Instructions that complete an address loaded with e_lis: operand holding the low half. */
	private static final Map<String, Integer> LOW_HALF_OPERAND =
		Map.of("e_add16i", 2, "e_addi", 2, "e_or2i", 1, "e_add2i.", 1);

	/** Small data area base registers and the linker symbols that define them. */
	private static final String[][] SMALL_DATA_BASES =
		{ { "r13", "_SDA_BASE_" }, { "r2", "_SDA2_BASE_" } };

	private static final int STARTUP_SEARCH_INSTRUCTIONS = 4;

	/** Bound on the code traced from each startup load. */
	private static final int MAX_REACHED_INSTRUCTIONS = 500_000;

	/** Shortest run of erased flash taken as the boundary between two programs. */
	private static final int MIN_ERASED_RUN = 16;

	/** Samples of a block searched for in the programs to find which one it copies. */
	private static final int COPY_SAMPLES = 8;
	private static final int COPY_SAMPLE_SIZE = 32;
	private static final int COPY_SAMPLE_DISTINCT = 8;

	private boolean assumeSmallDataBases = OPTION_DEFAULT_SDA;
	private boolean recoverSwitchTables = SWITCH_OPTION_DEFAULT_VALUE;

	/** The executable memory for which the small data area bases were last assumed. */
	private AddressSetView smallDataBasesCheckedFor;

	public E200ConstantPropagation() {
		super(PROCESSOR_NAME);
	}

	@Override
	public boolean canAnalyze(Program program) {
		if (!E200Analyzer.LANGUAGE_ID.equals(program.getLanguageID().getIdAsString())) {
			return false;
		}
		// the defaults the base analyzer derives from the address space
		checkPointerParamRefsOption = false;
		checkStoredRefsOption = true;
		checkParamRefsOption = true;
		long size = program.getAddressFactory().getDefaultAddressSpace().getSize();
		minSpeculativeRefAddress = size * 16;
		maxSpeculativeRefAddress = size * 8;
		return true;
	}

	@Override
	public void registerOptions(Options options, Program program) {
		super.registerOptions(options, program);

		options.registerOption(OPTION_NAME_SDA, assumeSmallDataBases, null,
			OPTION_DESCRIPTION_SDA);
		options.registerOption(SWITCH_OPTION_NAME, recoverSwitchTables, null,
			SWITCH_OPTION_DESCRIPTION);
	}

	@Override
	public void optionsChanged(Options options, Program program) {
		super.optionsChanged(options, program);

		assumeSmallDataBases = options.getBoolean(OPTION_NAME_SDA, assumeSmallDataBases);
		recoverSwitchTables = options.getBoolean(SWITCH_OPTION_NAME, recoverSwitchTables);
	}

	@Override
	public boolean added(Program program, AddressSetView set, TaskMonitor monitor, MessageLog log)
			throws CancelledException {
		if (assumeSmallDataBases) {
			// first, and again when memory is added, such as dumps of more of the device
			AddressSetView code = E200Analyzer.executableMemory(program);
			if (!code.equals(smallDataBasesCheckedFor)) {
				smallDataBasesCheckedFor = code;
				assumeSmallDataBases(program, code, monitor);
			}
		}
		return super.added(program, set, monitor, log);
	}

	// ---- Small data area bases ------------------------------------------------------------

	/**
	 * Sets the small data area base registers in the executable memory where they have no
	 * values, which the loader, the user or an earlier analysis may have set. The outcome goes
	 * to the application log only; the analysis message log would show a dialog after every
	 * analysis.
	 */
	private void assumeSmallDataBases(Program program, AddressSetView code, TaskMonitor monitor)
			throws CancelledException {
		for (String[] base : SMALL_DATA_BASES) {
			monitor.checkCancelled();
			Register reg = program.getRegister(base[0]);
			if (reg == null) {
				continue;
			}
			AddressSet free = new AddressSet(code);
			AddressRangeIterator it =
				program.getProgramContext().getRegisterValueAddressRanges(reg);
			while (it.hasNext()) {
				free.delete(it.next());
			}
			if (free.isEmpty()) {
				continue;
			}
			String where = free.equals(code) ? "all executable memory" : describe(free);
			Long value = symbolValue(program, base[1]);
			if (value != null) {
				setValue(program, reg, free, value);
				Msg.info(this, "Assuming " + reg + " = 0x" + Long.toHexString(value) + " (" +
					base[1] + ") in " + where);
				continue;
			}
			SortedMap<Long, List<Address>> loads = findStartupLoads(program, reg, monitor);
			if (loads.size() == 1) {
				value = loads.firstKey();
				setValue(program, reg, free, value);
				Msg.info(this, "Assuming " + reg + " = 0x" + Long.toHexString(value) +
					" (startup code at " + loads.get(value) + ") in " + where);
			}
			else if (loads.size() > 1) {
				assumePerProgram(program, reg, loads, code, free, monitor);
			}
		}
	}

	/**
	 * Sets the values of a register that different startup code loads differently, as in an
	 * image with several separately linked programs such as a boot manager, a bootloader and an
	 * application. Each value applies to the program whose startup code loads it: the span of
	 * the code that the startup code reaches, extended to the erased flash that separates it
	 * from the next program. Code between programs without erased flash gets no value. A block
	 * with code of no program, such as code copied to RAM, gets the values of the program whose
	 * code it copies.
	 */
	private void assumePerProgram(Program program, Register reg,
			SortedMap<Long, List<Address>> loads, AddressSetView code, AddressSetView free,
			TaskMonitor monitor) throws CancelledException {
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
				free.intersects(block.getStart(), block.getEnd()) &&
				!covered.intersects(block.getStart(), block.getEnd())) {
				Long owner = copiedFrom(program.getMemory(), block, regions, monitor);
				if (owner != null) {
					regions.get(owner).add(block.getStart(), block.getEnd());
				}
			}
		}

		for (Map.Entry<Long, AddressSet> entry : regions.entrySet()) {
			AddressSet region = entry.getValue().intersect(free);
			if (region.isEmpty()) {
				continue;
			}
			long value = entry.getKey();
			setValue(program, reg, region, value);
			Msg.info(this, "Assuming " + reg + " = 0x" + Long.toHexString(value) +
				" (startup code at " + loads.get(value) + ") in " + describe(region));
		}
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

	private Long symbolValue(Program program, String name) {
		Symbol symbol = SymbolUtilities.getLabelOrFunctionSymbol(program, name,
			err -> Msg.info(this, err));
		return symbol == null ? null : symbol.getAddress().getOffset();
	}

	private static void setValue(Program program, Register reg, AddressSetView set, long value) {
		ProgramContext context = program.getProgramContext();
		BigInteger bigValue = BigInteger.valueOf(value & 0xffffffffL);
		for (AddressRange range : set) {
			try {
				context.setValue(reg, range.getMinAddress(), range.getMaxAddress(), bigValue);
			}
			catch (ContextChangeException e) {
				throw new AssertException(e); // not a context register
			}
		}
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
		for (AddressRange range : E200Analyzer.executableMemory(program)) {
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
				if (writes(ins, reg) || ins.getFlowType().isJump() ||
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

	private static boolean writes(Instruction ins, Register reg) {
		for (Object result : ins.getResultObjects()) {
			if (result instanceof Register r && r.contains(reg)) {
				return true;
			}
		}
		return false;
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

	// ---- Constant propagation ---------------------------------------------------------------

	@Override
	public AddressSet flowConstants(final Program program, Address flowStart,
			AddressSetView flowSet, final SymbolicPropogator symEval, final TaskMonitor monitor)
			throws CancelledException {

		ConstantPropagationContextEvaluator eval =
			new ConstantPropagationContextEvaluator(monitor, trustWriteMemOption) {

				@Override
				public boolean evaluateContextBefore(VarnodeContext context, Instruction instr) {
					return false;
				}

				@Override
				public boolean evaluateReference(VarnodeContext context, Instruction instr,
						int pcodeop, Address address, int size, DataType dataType,
						RefType refType) {

					if (refType.isJump() && refType.isComputed() &&
						program.getMemory().contains(address) && address.getOffset() != 0) {
						super.evaluateReference(context, instr, pcodeop, address, size, dataType,
							refType);
						// for branching instructions, if we have a good target, mark it
						// if this isn't straight code (thunk computation), let someone else
						// lay down the reference
						return !symEval.encounteredBranch();
					}

					// a register loaded with a constant, or with the upper half of an address,
					// is not a reference even when it looks like one
					if (CONSTANT_LOADS.contains(instr.getMnemonicString())) {
						return false;
					}

					// don't use the displacement of an absolute load or store as an address
					if (isLoadOrStore(instr)) {
						for (Object obj : instr.getOpObjects(1)) {
							if (obj instanceof Scalar scalar &&
								scalar.getUnsignedValue() == address.getOffset()) {
								return false;
							}
						}
					}

					return super.evaluateReference(context, instr, pcodeop, address, size,
						dataType, refType);
				}

				@Override
				public boolean evaluateDestination(VarnodeContext context,
						Instruction instruction) {
					if (instruction.getFlowType().isJump() &&
						COMPUTED_JUMPS.contains(instruction.getMnemonicString()) &&
						!checkAlreadyRecovered(program, instruction.getMinAddress())) {
						// record the destination that is unknown
						destSet.addRange(instruction.getMinAddress(), instruction.getMinAddress());
					}
					return false;
				}

				@Override
				public Long unknownValue(VarnodeContext context, Instruction instruction,
						Varnode node) {
					if (node.isRegister()) {
						Register reg = program.getRegister(node.getAddress());
						if (reg != null && reg.getName().equals("xer_so")) {
							return Long.valueOf(0);
						}
					}
					return null;
				}

				@Override
				public boolean followFalseConditionalBranches() {
					return true;
				}

				@Override
				public boolean evaluateSymbolicReference(VarnodeContext context, Instruction instr,
						Address address) {
					return false;
				}

				@Override
				public boolean allowAccess(VarnodeContext context, Address addr) {
					return trustWriteMemOption;
				}
			};

		eval.setTrustWritableMemory(trustWriteMemOption)
				.setMinSpeculativeOffset(minSpeculativeRefAddress)
				.setMaxSpeculativeOffset(maxSpeculativeRefAddress)
				.setMinStoreLoadOffset(minStoreLoadRefAddress)
				.setCreateComplexDataFromPointers(createComplexDataFromPointers);

		AddressSet resultSet = symEval.flowConstants(flowStart, flowSet, eval, true, monitor);

		if (recoverSwitchTables) {
			recoverSwitches(program, symEval, eval.getDestinationSet(), monitor);
		}

		return resultSet;
	}

	private static boolean isLoadOrStore(Instruction instr) {
		String mnemonic = instr.getMnemonicString();
		int underscore = mnemonic.indexOf('_');
		if (mnemonic.startsWith("e_") || mnemonic.startsWith("se_")) {
			mnemonic = mnemonic.substring(underscore + 1);
		}
		return mnemonic.startsWith("l") || mnemonic.startsWith("st");
	}

	private static boolean checkAlreadyRecovered(Program program, Address addr) {
		int referenceCountFrom = program.getReferenceManager().getReferenceCountFrom(addr);

		if (referenceCountFrom > 1) {
			return true;
		}
		Reference[] refs = program.getReferenceManager().getReferencesFrom(addr);
		if (refs.length == 1 && !refs[0].getReferenceType().isData()) {
			return true;
		}

		return false;
	}

	// ---- Switch tables ----------------------------------------------------------------------

	private void recoverSwitches(final Program program, SymbolicPropogator symEval,
			AddressSet destinationSet, TaskMonitor monitor) throws CancelledException {

		final List<Address> targetList = new ArrayList<>();

		// now handle symbolic execution assuming values!
		class SwitchEvaluator implements ContextEvaluator {

			private static final int STARTING_MAX_TABLE_SIZE = 64;

			Address targetSwitchAddr = null;
			boolean hitTheGuard = false;
			Long assumeValue = Long.valueOf(0);
			int tableSizeMax = STARTING_MAX_TABLE_SIZE;

			public void setGuard(boolean hitGuard) {
				hitTheGuard = hitGuard;
			}

			public void setAssume(Long assume) {
				assumeValue = assume;
			}

			public void setTargetSwitchAddr(Address addr) {
				targetSwitchAddr = addr;
				tableSizeMax = STARTING_MAX_TABLE_SIZE;
			}

			public int getMaxTableSize() {
				return tableSizeMax;
			}

			@Override
			public boolean evaluateContextBefore(VarnodeContext context, Instruction instr) {
				return false;
			}

			@Override
			public boolean evaluateContext(VarnodeContext context, Instruction instr) {
				// the compare against the largest index sets the size of the table
				if (SWITCH_GUARDS.contains(instr.getMnemonicString())) {
					int numOps = instr.getNumOperands();
					if (numOps > 1) {
						Register reg = instr.getRegister(numOps - 2);
						Scalar scalar = instr.getScalar(numOps - 1);
						if (reg != null && scalar != null) {
							int newTableSizeMax = (int) scalar.getSignedValue() + 1;
							if (newTableSizeMax > 0 && newTableSizeMax < 128) {
								tableSizeMax = newTableSizeMax;
							}
							hitTheGuard = true;
							context.clearRegister(reg);
						}
					}
				}
				if (instr.getFlowType().isConditional()) {
					hitTheGuard = true;
				}

				return false;
			}

			@Override
			public Address evaluateConstant(VarnodeContext context, Instruction instr, int pcodeop,
					Address constant, int size, DataType dataType, RefType refType) {
				return null;
			}

			@Override
			public boolean evaluateReference(VarnodeContext context, Instruction instr, int pcodeop,
					Address address, int size, DataType dataType, RefType refType) {

				if (!((refType.isComputed() || refType.isConditional()) &&
					program.getMemory().contains(address))) {
					if (refType.isRead()) {
						createUndefinedData(program, address, size);
					}
					return false;
				}
				if (!targetList.contains(address)) {
					targetList.add(address);
				}
				return true; // just go ahead and mark up the instruction
			}

			@Override
			public boolean evaluateDestination(VarnodeContext context, Instruction instruction) {
				return instruction.getMinAddress().equals(targetSwitchAddr);
			}

			@Override
			public boolean evaluateReturn(Varnode retVN, VarnodeContext context,
					Instruction instruction) {
				return false;
			}

			@Override
			public Long unknownValue(VarnodeContext context, Instruction instruction,
					Varnode node) {
				if (node.isRegister()) {
					if (instruction.getFlowType().isJump()) {
						return null;
					}
					Register reg = program.getRegister(node.getAddress());
					if (reg != null) {
						// never assume for flags, or control registers
						if (reg.getName().equals("xer_so") || reg.getName().startsWith("cr")) {
							return Long.valueOf(0);
						}
					}
					if (hitTheGuard) {
						return assumeValue;
					}
				}
				return null;
			}

			@Override
			public boolean followFalseConditionalBranches() {
				return false;
			}

			@Override
			public boolean evaluateSymbolicReference(VarnodeContext context, Instruction instr,
					Address address) {
				return false;
			}

			@Override
			public boolean allowAccess(VarnodeContext context, Address addr) {
				// switch tables of flash images are often in a writable block
				return trustWriteMemOption;
			}
		}

		SwitchEvaluator switchEvaluator = new SwitchEvaluator();

		// for each unknown branch destination, flow the simple block of the branch
		AddressIterator iter = destinationSet.getAddresses(true);
		SimpleBlockModel model = new SimpleBlockModel(program);
		while (iter.hasNext() && !monitor.isCancelled()) {
			Address loc = iter.next();
			targetList.clear();

			// first see if something else has already done this!
			int referenceCountFrom = program.getReferenceManager().getReferenceCountFrom(loc);
			if (referenceCountFrom > 2) {
				continue;
			}

			CodeBlock bl = model.getFirstCodeBlockContaining(loc, monitor);
			if (bl == null) {
				continue;
			}

			AddressSet branchSet = new AddressSet(bl);
			CodeBlockReferenceIterator bliter = bl.getSources(monitor);
			boolean oneSource = (bl.getNumSources(monitor) == 1);
			while (bliter.hasNext()) {
				CodeBlockReference sbl = bliter.next();
				if (sbl.getFlowType().isCall()) {
					continue;
				}
				if ((sbl.getFlowType().isFallthrough() || oneSource) ||
					!sbl.getFlowType().isConditional()) {
					CodeBlock source = sbl.getSourceBlock();
					if (source != null) {
						branchSet.add(source);
					}
				}
			}

			switchEvaluator.setTargetSwitchAddr(loc);
			for (long assume = 0; assume < switchEvaluator.getMaxTableSize(); assume++) {
				switchEvaluator.setAssume(Long.valueOf(assume));
				switchEvaluator.setGuard(false);

				symEval.flowConstants(branchSet.getMinAddress(), branchSet, switchEvaluator, false,
					monitor);
				// if it didn't get it after try with 0
				if (assume > 0 && targetList.size() < 1) {
					break;
				}
				if (symEval.readExecutable()) {
					break;
				}
			}
			// re-create the function body with the newly found code
			if (targetList.size() > 1) {
				AddressTable table = new AddressTable(loc, targetList.toArray(new Address[0]),
					program.getDefaultPointerSize(), 0, false);
				table.fixupFunctionBody(program, program.getListing().getInstructionAt(loc),
					monitor);
				labelTable(program, loc, targetList);
			}
			else if (targetList.size() == 1) {
				Function f = program.getFunctionManager().getFunctionContaining(loc);
				if (f != null) {
					CreateFunctionCmd.fixupFunctionBody(program, f, monitor);
				}
			}
		}
	}

	private static void createUndefinedData(Program program, Address address, int size) {
		if (size < 1 || size > 8 || !program.getListing().isUndefined(address, address)) {
			return;
		}
		try {
			program.getListing().createData(address, Undefined.getUndefinedDataType(size));
		}
		catch (CodeUnitInsertionException e) {
			// ignore
		}
	}

	private static void labelTable(Program program, Address loc, List<Address> targets) {
		Namespace space = null;

		String spaceName = "switch_" + loc;
		try {
			space = program.getSymbolTable().createNameSpace(space, spaceName, SourceType.ANALYSIS);
		}
		catch (DuplicateNameException e) {
			space = program.getSymbolTable().getNamespace(spaceName, program.getGlobalNamespace());
		}
		catch (InvalidInputException e) {
			// just go with default space
		}

		int tableNumber = 0;
		for (Address addr : targets) {
			AddLabelCmd lcmd = new AddLabelCmd(addr, "case_" + Long.toHexString(tableNumber), space,
				SourceType.ANALYSIS);
			tableNumber++;
			lcmd.setNamespace(space);

			lcmd.applyTo(program);
		}
	}
}
