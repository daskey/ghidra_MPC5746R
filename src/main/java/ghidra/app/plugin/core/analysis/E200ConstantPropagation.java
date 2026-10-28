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
import ghidra.app.util.importer.MessageLog;
import ghidra.framework.options.Options;
import ghidra.program.model.address.*;
import ghidra.program.model.block.*;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.Undefined;
import ghidra.program.model.lang.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.program.util.*;
import ghidra.util.exception.*;
import ghidra.util.task.TaskMonitor;

/**
 * Constant propagation for the NXP e200z4 VLE language ({@code PowerPC:BE:32:VLE-e200}), part
 * of {@link E200Analyzer}. It is derived from Ghidra's {@code PowerPCAddressAnalyzer}, which
 * the language's processor spec disables, and is not an analyzer of its own: Ghidra finds
 * analyzers by the end of their class names. Compared with that analyzer it:
 * <ul>
 * <li>recognizes VLE instructions: no references from {@code e_lis} (the upper half of an
 * address) or from {@code e_li}, {@code se_li}, {@code se_bgeni} and {@code se_bmaski}
 * constants, and switch table recovery at {@code se_bctr} with VLE compares as the guard</li>
 * <li>reads switch tables from writable memory when values from writable memory are trusted,
 * as for flash images loaded into a single read/write block</li>
 * <li>drops the PEF and ELF function descriptor (r2/r30) handling, which does not apply to
 * the e200 EABI</li>
 * <li>adds references to arrays whose address code splits around the index</li>
 * </ul>
 * It works with the small data area bases {@link E200SmallDataBases} sets, and makes the
 * references of the instructions that use them again where they change.
 */
final class E200ConstantPropagation extends ConstantPropagationAnalyzer {

	private static final String SWITCH_OPTION_NAME = "Switch Table Recovery";
	private static final String SWITCH_OPTION_DESCRIPTION = "Turn on to recover switch tables";
	private static final boolean SWITCH_OPTION_DEFAULT_VALUE = true;

	/** Instructions that only load a constant, never a complete address. */
	private static final Set<String> CONSTANT_LOADS =
		Set.of("e_li", "se_li", "li", "e_lis", "lis", "se_bgeni", "se_bmaski");

	/** Indirect branches through CTR that may be switches. */
	private static final Set<String> COMPUTED_JUMPS = Set.of("se_bctr", "bctr", "bcctr");

	/** Instructions searched after the lower half of a split array address for the upper */
	private static final int SPLIT_BASE_INSTRUCTIONS = 4;

	/** Registers that hold no index: the stack pointer and the small data area bases */
	private static final Set<String> NOT_INDEXES = Set.of("r1", "r2", "r13");

	/** Compares whose immediate bounds a switch index. */
	private static final Set<String> SWITCH_GUARDS = Set.of("e_cmpli", "e_cmpi", "e_cmpl16i",
		"e_cmp16i", "se_cmpli", "se_cmpi", "cmpli", "cmplwi", "cmpi", "cmpwi");

	private boolean recoverSwitchTables = SWITCH_OPTION_DEFAULT_VALUE;

	public E200ConstantPropagation() {
		super(E200Analyzer.NAME);
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

		options.registerOption(SWITCH_OPTION_NAME, recoverSwitchTables, null,
			SWITCH_OPTION_DESCRIPTION);
	}

	@Override
	public void optionsChanged(Options options, Program program) {
		super.optionsChanged(options, program);

		recoverSwitchTables = options.getBoolean(SWITCH_OPTION_NAME, recoverSwitchTables);
	}

	@Override
	public boolean added(Program program, AddressSetView set, TaskMonitor monitor, MessageLog log)
			throws CancelledException {
		boolean ok = super.added(program, set, monitor, log);
		addSplitBaseReferences(program, set, monitor);
		return ok;
	}

	/**
	 * Adds references to the base addresses of arrays whose address code splits around the
	 * index, {@code rD = rIdx + lo} ({@code e_add16i} or {@code e_addi}) and then
	 * {@code rD += ha << 16} ({@code e_add2is}): constant propagation sees no address in
	 * either instruction.
	 */
	private static void addSplitBaseReferences(Program program, AddressSetView set,
			TaskMonitor monitor) throws CancelledException {
		ReferenceManager references = program.getReferenceManager();
		for (Instruction low : program.getListing().getInstructions(set, true)) {
			monitor.checkCancelled();
			Instruction high = splitBaseHigh(low);
			if (high == null) {
				continue;
			}
			long upper = high.getScalar(1).getValue() << 16;
			long base = (upper + (short) low.getScalar(2).getValue()) & 0xffffffffL;
			Address target = base == 0 ? null
					: program.getAddressFactory().getDefaultAddressSpace().getAddress(base);
			if (target != null && program.getMemory().contains(target) &&
				references.getReference(high.getMinAddress(), target, 1) == null) {
				references.addMemoryReference(high.getMinAddress(), target, RefType.DATA,
					SourceType.ANALYSIS, 1);
			}
		}
	}

	/**
	 * The {@code e_add2is} that adds the upper half of an address to the register an
	 * {@code e_add16i} or {@code e_addi} adds the lower half to an index in, within a few
	 * instructions and no flow or other write between; null if there is none. Adds to r1, the
	 * stack pointer, and to the small data area bases r2 and r13 are not of arrays.
	 */
	private static Instruction splitBaseHigh(Instruction low) {
		String mnemonic = low.getMnemonicString();
		if (!mnemonic.equals("e_add16i") && !mnemonic.equals("e_addi")) {
			return null;
		}
		Register rD = low.getRegister(0);
		Register rA = low.getRegister(1);
		if (rD == null || rA == null || low.getScalar(2) == null ||
			NOT_INDEXES.contains(rA.getName())) {
			return null;
		}
		Instruction next = low;
		for (int i = 0; i < SPLIT_BASE_INSTRUCTIONS; i++) {
			next = next.getNext();
			if (next == null || next.getFlowType().isJump() || next.getFlowType().isCall() ||
				next.getFlowType().isTerminal()) {
				return null;
			}
			if (next.getMnemonicString().equals("e_add2is")) {
				return rD.equals(next.getRegister(0)) && next.getScalar(1) != null ? next : null;
			}
			if (E200Code.writes(next, rD)) {
				return null;
			}
		}
		return null;
	}

	/**
	 * Removes the references that analysis made with the earlier value of a small data area
	 * base, from the instructions that read it where it changed: those to the 64 KB that a
	 * displacement from the earlier base reaches, but not from the new one. Returns the
	 * instructions that read a changed base, for constant propagation to make their
	 * references with the new values.
	 */
	static AddressSet forget(Program program, List<E200SmallDataBases.Change> changes,
			TaskMonitor monitor) throws CancelledException {
		AddressSet instructions = new AddressSet();
		ReferenceManager references = program.getReferenceManager();
		for (E200SmallDataBases.Change change : changes) {
			for (Instruction instruction : program.getListing()
					.getInstructions(new AddressSet(change.range()), true)) {
				monitor.checkCancelled();
				if (!E200Code.reads(instruction, change.register())) {
					continue;
				}
				instructions.add(instruction.getMinAddress(), instruction.getMaxAddress());
				for (Reference ref : references.getReferencesFrom(instruction.getMinAddress())) {
					long target = ref.getToAddress().getOffset();
					if (ref.getSource() == SourceType.ANALYSIS &&
						!ref.getReferenceType().isFlow() && reaches(change.before(), target) &&
						!reaches(change.after(), target)) {
						references.delete(ref);
					}
				}
			}
		}
		return instructions;
	}

	/** Whether a signed 16-bit displacement from a base reaches an address */
	private static boolean reaches(BigInteger base, long address) {
		long displacement = base == null ? Long.MAX_VALUE : address - base.longValue();
		return displacement >= Short.MIN_VALUE && displacement <= Short.MAX_VALUE;
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
