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
 * Constant reference analyzer for the NXP e200z4 VLE language ({@code PowerPC:BE:32:VLE-e200}),
 * derived from Ghidra's {@code PowerPCAddressAnalyzer}, which the language's processor spec
 * disables. Compared with that analyzer it:
 * <ul>
 * <li>assumes the EABI small data area bases in r13 ({@code _SDA_BASE_}) and r2
 * ({@code _SDA2_BASE_}) in all code, taken from existing register values, the symbols, or the
 * startup code that loads them, so that small data accesses resolve to addresses</li>
 * <li>recognizes VLE instructions: no references from {@code e_lis} (the upper half of an
 * address) or from {@code e_li}, {@code se_li}, {@code se_bgeni} and {@code se_bmaski}
 * constants, and switch table recovery at {@code se_bctr} with VLE compares as the guard</li>
 * <li>reads switch tables from writable memory when values from writable memory are trusted,
 * as for flash images loaded into a single read/write block</li>
 * <li>drops the PEF and ELF function descriptor (r2/r30) handling, which does not apply to
 * the e200 EABI</li>
 * </ul>
 */
public class E200AddressAnalyzer extends ConstantPropagationAnalyzer {

	/** Language handled by this analyzer. */
	public static final String LANGUAGE_ID = "PowerPC:BE:32:VLE-e200";

	private static final String PROCESSOR_NAME = "PowerPC e200";

	private static final String OPTION_NAME_SDA = "Assume small data area bases";
	private static final String OPTION_DESCRIPTION_SDA =
		"Assume the EABI small data area base registers r13 (_SDA_BASE_) and r2 (_SDA2_BASE_)\n" +
			"in all executable memory, unless they already have values there. The values come\n" +
			"from the _SDA_BASE_ and _SDA2_BASE_ symbols or from the startup code that loads\n" +
			"the registers, when there is only one such value.";
	private static final boolean OPTION_DEFAULT_SDA = true;

	private static final String OPTION_NAME_MARK_DUAL_INSTRUCTION =
		"Mark dual instruction references";
	private static final String OPTION_DESCRIPTION_MARK_DUAL_INSTRUCTION =
		"Turn on to mark all potential dual instruction references\n" +
			"(e_lis followed by e_add16i, e_addi, e_or2i or e_add2i.)\n" +
			"even if they are not seen to be used as a reference.";
	private static final boolean OPTION_DEFAULT_MARK_DUAL_INSTRUCTION = false;

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

	private boolean assumeSmallDataBases = OPTION_DEFAULT_SDA;
	private boolean markupDualInstructionOption = OPTION_DEFAULT_MARK_DUAL_INSTRUCTION;
	private boolean recoverSwitchTables = SWITCH_OPTION_DEFAULT_VALUE;

	private boolean smallDataBasesChecked;

	public E200AddressAnalyzer() {
		super(PROCESSOR_NAME);
	}

	@Override
	public boolean canAnalyze(Program program) {
		if (!LANGUAGE_ID.equals(program.getLanguageID().getIdAsString())) {
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
		options.registerOption(OPTION_NAME_MARK_DUAL_INSTRUCTION, markupDualInstructionOption, null,
			OPTION_DESCRIPTION_MARK_DUAL_INSTRUCTION);
		options.registerOption(SWITCH_OPTION_NAME, recoverSwitchTables, null,
			SWITCH_OPTION_DESCRIPTION);
	}

	@Override
	public void optionsChanged(Options options, Program program) {
		super.optionsChanged(options, program);

		assumeSmallDataBases = options.getBoolean(OPTION_NAME_SDA, assumeSmallDataBases);
		markupDualInstructionOption =
			options.getBoolean(OPTION_NAME_MARK_DUAL_INSTRUCTION, markupDualInstructionOption);
		recoverSwitchTables = options.getBoolean(SWITCH_OPTION_NAME, recoverSwitchTables);
	}

	@Override
	public boolean added(Program program, AddressSetView set, TaskMonitor monitor, MessageLog log)
			throws CancelledException {
		if (assumeSmallDataBases && !smallDataBasesChecked) {
			smallDataBasesChecked = true;
			assumeSmallDataBases(program, monitor, log);
		}
		return super.added(program, set, monitor, log);
	}

	// ---- Small data area bases ------------------------------------------------------------

	private void assumeSmallDataBases(Program program, TaskMonitor monitor, MessageLog log)
			throws CancelledException {
		AddressSetView code = executableMemory(program);
		if (code.isEmpty()) {
			return;
		}
		for (String[] base : SMALL_DATA_BASES) {
			monitor.checkCancelled();
			Register reg = program.getRegister(base[0]);
			if (reg == null || hasValues(program, reg, code)) {
				continue; // set by the loader or the user
			}
			String source = base[1];
			Long value = symbolValue(program, base[1]);
			if (value == null) {
				SortedMap<Long, List<Address>> loads = findStartupLoads(program, reg, monitor);
				if (loads.size() != 1) {
					if (loads.size() > 1) {
						String msg = "Not assuming " + reg + ": the startup code loads " +
							"different values " + describe(loads) + "; set its value with " +
							"Set Register Values";
						log.appendMsg(getName(), msg);
						Msg.warn(this, msg);
					}
					continue;
				}
				value = loads.firstKey();
				source = "startup code at " + loads.get(value);
			}
			setValue(program, reg, code, value);
			String msg = "Assuming " + reg + " = 0x" + Long.toHexString(value) + " (" + source +
				") in all executable memory";
			log.appendMsg(getName(), msg);
			Msg.info(this, msg);
		}
	}

	/**
	 * Executable memory with initialized bytes, or all initialized memory if no block is
	 * marked executable.
	 */
	private static AddressSetView executableMemory(Program program) {
		Memory memory = program.getMemory();
		AddressSet set = new AddressSet();
		for (MemoryBlock block : memory.getBlocks()) {
			if (block.isExecute() && block.isInitialized()) {
				set.add(block.getStart(), block.getEnd());
			}
		}
		if (set.isEmpty()) {
			set.add(memory.getLoadedAndInitializedAddressSet());
		}
		return set;
	}

	private static boolean hasValues(Program program, Register reg, AddressSetView set) {
		AddressRangeIterator it = program.getProgramContext().getRegisterValueAddressRanges(reg);
		while (it.hasNext()) {
			AddressRange range = it.next();
			if (set.intersects(range.getMinAddress(), range.getMaxAddress())) {
				return true;
			}
		}
		return false;
	}

	private Long symbolValue(Program program, String name) {
		Symbol symbol = SymbolUtilities.getLabelOrFunctionSymbol(program, name,
			err -> Msg.warn(this, err));
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
		for (AddressRange range : executableMemory(program)) {
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
					if (value != null) {
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

	private static String describe(SortedMap<Long, List<Address>> loads) {
		StringBuilder sb = new StringBuilder();
		loads.forEach((value, at) -> sb.append(sb.length() == 0 ? "" : ", ")
				.append("0x")
				.append(Long.toHexString(value))
				.append(" at ")
				.append(at));
		return sb.toString();
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
				public boolean evaluateContext(VarnodeContext context, Instruction instr) {
					if (markupDualInstructionOption) {
						markupDualInstruction(program, context, instr);
					}
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

	/**
	 * Marks the operand that completes an address loaded with e_lis (e_add16i, e_or2i, ...),
	 * even where the address is not seen to be used.
	 */
	private static void markupDualInstruction(Program program, VarnodeContext context,
			Instruction instr) {
		Integer lowOperand = LOW_HALF_OPERAND.get(instr.getMnemonicString());
		if (lowOperand == null) {
			return;
		}
		Register reg = instr.getRegister(0);
		if (reg == null) {
			return;
		}
		BigInteger val = context.getValue(reg, false);
		if (val == null) {
			return;
		}
		long lval = val.longValue();
		Address refAddr = instr.getMinAddress().getNewTruncatedAddress(lval, true);
		if ((lval > 4096 || lval < 0) && program.getMemory().contains(refAddr) &&
			instr.getOperandReferences(lowOperand).length == 0) {
			instr.addOperandReference(lowOperand, refAddr, RefType.DATA, SourceType.ANALYSIS);
		}
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
