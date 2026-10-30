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

import ghidra.app.cmd.disassemble.DisassembleCommand;
import ghidra.app.util.PseudoDisassembler;
import ghidra.app.util.PseudoInstruction;
import ghidra.framework.options.Options;
import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.*;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.symbol.FlowType;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Finds the entry points of MPC57xx flash images (part of {@link E200Analyzer}): the reset
 * vectors in boot headers and the interrupt vectors, at the start of every analysis. A raw
 * flash image has no other entry points, and startup code usually reaches the interrupt setup
 * only through values that analysis cannot follow. What is marked up already is left as it
 * is.
 * <ul>
 * <li>Boot headers: the boot assist flash looks for a boot header at the start of flash
 * blocks. Its first word holds the boot identifier 0x5A in bits 8-15 ({@code 0x005A....}),
 * and the words at offsets 0x10-0x1C hold the reset vectors of the cores, or 0 for a core
 * that is not started. Checked at the start of each memory block and every 16 KB.</li>
 * <li>Interrupt vector tables: the e200z4 has fixed vector offsets from IVPR, 16 bytes
 * apart, and each vector in use runs straight to an {@code e_b} to its handler, at its start
 * or after register setup that does not access memory (an {@code e_li} of the vector's
 * number before an {@code e_b} to the common entry of an operating system). A table is taken
 * to be at least {@link #MIN_VECTORS} such vectors from a 256-byte boundary. The vectors are
 * labeled ({@code IVOR4_ExternalInput}, ...), the handlers become functions, and the padding
 * after each branch that decodes as instructions is disassembled.</li>
 * <li>Hardware vectors of the interrupt controller: in hardware vector mode, the core
 * branches to IVPR + 0x1000 + 4 times the interrupt source's number, where an {@code e_b}
 * leads to the source's entry. After a vector table, words there that are all erased or
 * {@code e_b} are such vectors: labeled {@code INTC_vector_<number>}, with the entries
 * functions.</li>
 * </ul>
 */
final class E200EntryPoints {

	private static final String OPTION_NAME = "Find boot headers and interrupt vectors";
	private static final String OPTION_DESCRIPTION =
		"Find the entry points of MPC57xx flash images: the reset vectors in boot\n" +
			"headers (a word 0x005A.... at the start of a block or a 16 KB boundary) and\n" +
			"interrupt vector tables (e_b instructions 16 bytes apart), and disassemble\n" +
			"them as functions.";

	private static final int BOOT_ID = 0x005A;

	/** Boot headers are searched for at multiples of the smallest flash block. */
	private static final int HEADER_ALIGNMENT = 0x4000;

	private static final int VECTORS_OFFSET = 0x10;
	private static final int VECTOR_COUNT = 4;
	private static final int HEADER_SIZE = VECTORS_OFFSET + 4 * VECTOR_COUNT;

	/** IVPR holds the upper 24 bits of the vector table address. */
	private static final int TABLE_ALIGNMENT = 0x100;
	private static final int VECTOR_SPACING = 0x10;

	/**
	 * Fewest vectors taken as a table. Startup code fills at least the first dozen vectors
	 * (IVOR0-IVOR11), usually all 16.
	 */
	private static final int MIN_VECTORS = 8;

	/** The e200z4 interrupts, in the order of their vectors. */
	private static final String[] IVORS = { "IVOR0_CriticalInput", "IVOR1_MachineCheck",
		"IVOR2_DataStorage", "IVOR3_InstructionStorage", "IVOR4_ExternalInput",
		"IVOR5_Alignment", "IVOR6_Program", "IVOR7_FloatingPointUnavailable", "IVOR8_SystemCall",
		"IVOR9_AuxiliaryProcessorUnavailable", "IVOR10_Decrementer", "IVOR11_FixedIntervalTimer",
		"IVOR12_WatchdogTimer", "IVOR13_DataTlbError", "IVOR14_InstructionTlbError",
		"IVOR15_Debug", "IVOR32_EfpuUnavailable", "IVOR33_EfpuDataException",
		"IVOR34_EfpuRoundException" };

	private boolean enabled = true;

	void registerOptions(Options options) {
		options.registerOption(OPTION_NAME, enabled, null, OPTION_DESCRIPTION);
	}

	void optionsChanged(Options options) {
		enabled = options.getBoolean(OPTION_NAME, enabled);
	}

	/** Finds the entry points in initialized memory, and marks up those that are not yet. */
	void find(Program program, TaskMonitor monitor) throws CancelledException {
		if (!enabled) {
			return;
		}
		for (MemoryBlock block : program.getMemory().getBlocks()) {
			monitor.checkCancelled();
			if (block.isInitialized()) {
				findBootHeaders(program, block);
			}
		}
		List<Table> tables = new ArrayList<>();
		for (AddressRange range : E200Code.executableMemory(program)) {
			tables.addAll(findVectorTables(program, range, monitor));
		}
		PseudoDisassembler disassembler = new PseudoDisassembler(program);
		for (Table table : tables) {
			monitor.checkCancelled();
			markVectorTable(program, disassembler, table);
			markHardwareVectors(program, disassembler, table, tables, monitor);
		}
	}

	// ---- Boot headers -----------------------------------------------------------------------

	private void findBootHeaders(Program program, MemoryBlock block) {
		if (block.getSize() < HEADER_SIZE) {
			return;
		}
		Address last = block.getEnd().subtract(HEADER_SIZE - 1);
		Set<Address> candidates = new LinkedHashSet<>();
		candidates.add(block.getStart());
		long first = (block.getStart().getOffset() + HEADER_ALIGNMENT - 1) & -HEADER_ALIGNMENT;
		for (long offset = first; offset <= last.getOffset(); offset += HEADER_ALIGNMENT) {
			candidates.add(block.getStart().getNewAddress(offset));
		}
		for (Address header : candidates) {
			if (header.compareTo(last) <= 0) {
				markBootHeader(program, header);
			}
		}
	}

	/** Marks up the boot header at {@code header}, if there is one, and its reset vectors. */
	private void markBootHeader(Program program, Address header) {
		Memory memory = program.getMemory();
		List<Address> vectors = new ArrayList<>();
		try {
			if ((memory.getInt(header) >>> 16) != BOOT_ID) {
				return;
			}
			for (int i = 0; i < VECTOR_COUNT; i++) {
				long value = memory.getInt(header.add(VECTORS_OFFSET + 4 * i)) & 0xffffffffL;
				vectors.add(resetVector(program, header, value));
			}
		}
		catch (MemoryAccessException | AddressOutOfBoundsException e) {
			return;
		}
		Set<Address> distinct = new HashSet<>(vectors);
		distinct.remove(null);
		if (distinct.isEmpty()) {
			return;
		}

		if (program.getListing().isUndefined(header, header.add(HEADER_SIZE - 1))) {
			try {
				program.getListing().createData(header, bootHeaderType(program));
			}
			catch (CodeUnitInsertionException e) {
				// something is already defined there
			}
		}
		E200Data.label(program, header, "boot_header", SourceType.ANALYSIS);

		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		for (int i = 0; i < VECTOR_COUNT; i++) {
			Address vector = vectors.get(i);
			if (vector == null || vectors.indexOf(vector) != i ||
				program.getFunctionManager().getFunctionAt(vector) != null) {
				continue; // no vector, the same as an earlier core's, or marked up already
			}
			E200Data.label(program, vector, distinct.size() == 1 ? "reset" : "reset_" + i,
				SourceType.ANALYSIS);
			program.getSymbolTable().addExternalEntryPoint(vector);
			manager.disassemble(vector);
			manager.createFunction(vector, false);
			Msg.info(E200Analyzer.class, "Boot header at " + header + ": reset vector " + vector);
		}
	}

	/** The address of a reset vector, or null if it does not point to code in memory. */
	private static Address resetVector(Program program, Address header, long value) {
		if (value == 0 || value == 0xffffffffL || (value & 1) != 0) {
			return null;
		}
		Address target = header.getNewAddress(value);
		MemoryBlock block = program.getMemory().getBlock(target);
		if (block == null || !block.isInitialized()) {
			return null;
		}
		return new PseudoDisassembler(program).isValidCode(target) ? target : null;
	}

	private static DataType bootHeaderType(Program program) {
		StructureDataType struct =
			new StructureDataType(CategoryPath.ROOT, "MPC57xx_boot_header", 0);
		struct.add(DWordDataType.dataType, "config", "boot identifier 0x5A in bits 8-15");
		struct.add(new ArrayDataType(DWordDataType.dataType, 3, 4), "reserved", null);
		struct.add(new ArrayDataType(new Pointer32DataType(), VECTOR_COUNT, 4), "reset_vector",
			"reset vectors of the cores, 0 for a core that is not started");
		return program.getDataTypeManager()
				.resolve(struct, DataTypeConflictHandler.DEFAULT_HANDLER);
	}

	// ---- Interrupt vectors ------------------------------------------------------------------

	/**
	 * The interrupt controller's hardware vectors, in hardware vector mode: an {@code e_b}
	 * per interrupt source at IVPR + 0x1000 + 4 times the source's number
	 */
	private static final int HARDWARE_VECTORS_OFFSET = 0x1000;
	private static final int HARDWARE_VECTORS = 1024;
	/** How far the entry of a hardware vector may run before it branches to a common entry */
	private static final int MAX_ENTRY_LENGTH = 32;

	/** A vector table: its address and the branch each of its vectors runs to */
	private record Table(Address start, List<Branch> vectors) {
		Address end() {
			return start.add(vectors.size() * VECTOR_SPACING - 1);
		}
	}

	/** An unconditional branch: where it is, its length and its target */
	private record Branch(Address at, int length, Address target) {
	}

	private List<Table> findVectorTables(Program program, AddressRange range,
			TaskMonitor monitor) throws CancelledException {
		PseudoDisassembler disassembler = new PseudoDisassembler(program);
		List<Table> tables = new ArrayList<>();
		long first = range.getMinAddress().getOffset();
		long start = (first + TABLE_ALIGNMENT - 1) & -TABLE_ALIGNMENT;
		long end = range.getMaxAddress().getOffset();
		for (long offset = start; offset + MIN_VECTORS * VECTOR_SPACING - 1 <= end;
				offset += TABLE_ALIGNMENT) {
			monitor.checkCancelled();
			Address table = range.getMinAddress().getNewAddress(offset);
			if (offset - VECTOR_SPACING >= first && branch(program, disassembler,
				table.subtract(VECTOR_SPACING), VECTOR_SPACING) != null) {
				continue; // inside a longer run of vectors
			}
			List<Branch> vectors = new ArrayList<>();
			for (int i = 0; i <= IVORS.length; i++) {
				Branch vector = offset + (i + 1) * VECTOR_SPACING - 1 > end ? null
						: branch(program, disassembler, table.add(i * VECTOR_SPACING),
							VECTOR_SPACING);
				if (vector == null) {
					break;
				}
				vectors.add(vector);
			}
			// more branches than there are vectors: some other kind of table
			if (vectors.size() >= MIN_VECTORS && vectors.size() <= IVORS.length) {
				tables.add(new Table(table, vectors));
			}
		}
		return tables;
	}

	/**
	 * The first {@code e_b} that the code from {@code start} runs to within {@code length}
	 * bytes, to initialized memory: the branch of a vector, at its start or after setting up
	 * registers, as an {@code e_li} of the vector's number before an {@code e_b} to a common
	 * entry. Null where a call, a return, a computed branch, an access to memory, a
	 * {@code se_b} (the end of a short case of a switch) or bytes that do not decode come
	 * first, or the code runs past the bytes.
	 */
	private static Branch branch(Program program, PseudoDisassembler disassembler,
			Address start, int length) {
		Address last;
		try {
			last = start.addNoWrap(length - 1);
		}
		catch (AddressOverflowException e) {
			return null;
		}
		Address a = start;
		while (a != null && a.compareTo(last) <= 0) {
			PseudoInstruction instruction;
			try {
				instruction = disassembler.disassemble(a);
			}
			catch (Exception e) {
				return null;
			}
			if (instruction == null || instruction.getMaxAddress().compareTo(last) > 0) {
				return null;
			}
			FlowType flow = instruction.getFlowType();
			if (flow.isCall() || flow.isTerminal() || flow.isComputed()) {
				return null;
			}
			if (flow.isJump() && flow.isUnConditional()) {
				// an e_b, which reaches anywhere; se_b ends the short cases of a switch
				Address[] flows = instruction.getFlows();
				MemoryBlock block = flows.length == 1 && instruction.getLength() == 4
						? program.getMemory().getBlock(flows[0])
						: null;
				return block != null && block.isInitialized()
						? new Branch(a, instruction.getLength(), flows[0])
						: null;
			}
			for (PcodeOp op : instruction.getPcode()) {
				if (op.getOpcode() == PcodeOp.STORE || op.getOpcode() == PcodeOp.LOAD) {
					return null; // a vector sets up registers, it does not access memory
				}
			}
			a = instruction.getMaxAddress().next();
		}
		return null;
	}

	/**
	 * The target of the {@code e_b} (not {@code e_bl}) at {@code table + offset}, if it is in
	 * initialized memory. {@code e_b} is opcode 30 with bit 6 and LK clear; the displacement
	 * is bits 7-30.
	 */
	static Address branchTarget(Memory memory, Address table, int offset) {
		Address address;
		int word;
		try {
			address = table.addNoWrap(offset);
			word = memory.getInt(address);
		}
		catch (AddressOverflowException | MemoryAccessException e) {
			return null;
		}
		if ((word & 0xfe000001) != 0x78000000) {
			return null;
		}
		int displacement = ((word & 0x01fffffe) << 7) >> 7;
		Address target;
		try {
			target = address.addNoWrap(displacement);
		}
		catch (AddressOverflowException e) {
			return null;
		}
		MemoryBlock block = memory.getBlock(target);
		return block != null && block.isInitialized() ? target : null;
	}

	private void markVectorTable(Program program, PseudoDisassembler disassembler,
			Table table) {
		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		Listing listing = program.getListing();
		FunctionManager functions = program.getFunctionManager();
		Set<Address> handlers = new HashSet<>();
		boolean marked = false;
		for (int i = 0; i < table.vectors().size(); i++) {
			Address vector = table.start().add(i * VECTOR_SPACING);
			Branch branch = table.vectors().get(i);
			E200Data.label(program, vector, IVORS[i], SourceType.ANALYSIS);
			if (listing.getInstructionAt(vector) == null) {
				manager.disassemble(vector);
				marked = true;
			}
			marked |= disassembleRest(program, disassembler, branch.at().add(branch.length()),
				vector.add(VECTOR_SPACING - 1));
			Address handler = branch.target();
			if ((handler.compareTo(table.start()) < 0 || handler.compareTo(table.end()) > 0) &&
				functions.getFunctionAt(handler) == null && handlers.add(handler)) {
				manager.createFunction(handler, false);
				marked = true;
			}
		}
		if (marked) {
			Msg.info(E200Analyzer.class, "Interrupt vector table at " + table.start() + ": " +
				table.vectors().size() + " vectors");
		}
	}

	/**
	 * Disassembles the bytes of a vector after its branch, {@code start} to {@code end}, where
	 * all of them decode as instructions (the padding an assembler puts there, as
	 * {@code e_nop}, a branch to itself and {@code se_nop}); erased bytes stay as they are.
	 * Returns whether it did.
	 */
	private static boolean disassembleRest(Program program, PseudoDisassembler disassembler,
			Address start, Address end) {
		if (start.compareTo(end) > 0 || !program.getListing().isUndefined(start, end)) {
			return false;
		}
		Memory memory = program.getMemory();
		boolean erased = true;
		try {
			for (Address a = start; a.compareTo(end) <= 0; a = a.next()) {
				erased &= memory.getByte(a) == (byte) 0xff;
			}
		}
		catch (MemoryAccessException e) {
			return false;
		}
		if (erased) {
			return false;
		}
		for (Address a = start; a.compareTo(end) <= 0;) {
			PseudoInstruction instruction;
			try {
				instruction = disassembler.disassemble(a);
			}
			catch (Exception e) {
				return false;
			}
			if (instruction == null || instruction.getMaxAddress().compareTo(end) > 0 ||
				instruction.getMnemonicString().equals("se_illegal")) {
				return false;
			}
			a = instruction.getMaxAddress().next();
			if (a == null) {
				break;
			}
		}
		AddressSet rest = new AddressSet(start, end);
		new DisassembleCommand(rest, rest, true).applyTo(program);
		return true;
	}

	/**
	 * Marks up the interrupt controller's hardware vectors that follow a vector table, where
	 * the words from IVPR + 0x1000 on are erased or {@code e_b} instructions only, up to the
	 * next vector table: each {@code e_b} is the vector of one interrupt source, labeled
	 * {@code INTC_vector_<number>}, and the entry it branches to becomes a function. The
	 * entries usually load the source's number and branch on to a common entry, a dispatcher;
	 * a target that several entries branch to becomes a function first, so that the entries
	 * branch to it rather than take it in.
	 */
	private static void markHardwareVectors(Program program, PseudoDisassembler disassembler,
			Table table, List<Table> tables, TaskMonitor monitor) throws CancelledException {
		Memory memory = program.getMemory();
		Address first;
		try {
			first = table.start().addNoWrap(HARDWARE_VECTORS_OFFSET);
		}
		catch (AddressOverflowException e) {
			return;
		}
		Map<Address, Address> entries = new LinkedHashMap<>(); // by vector, the entry
		for (int n = 0; n < HARDWARE_VECTORS; n++) {
			monitor.checkCancelled();
			Address vector;
			int word;
			try {
				vector = first.addNoWrap(4L * n);
				word = memory.getInt(vector);
			}
			catch (AddressOverflowException | MemoryAccessException e) {
				break;
			}
			boolean another = false;
			for (Table t : tables) {
				another |= t != table && t.start().equals(vector);
			}
			if (another) {
				break; // the next vector table
			}
			if (word == -1 || word == 0) {
				continue; // no handler for the source
			}
			Address entry = branchTarget(memory, vector, 0);
			if (entry == null) {
				return; // code or data: no hardware vectors
			}
			entries.put(vector, entry);
		}
		if (entries.isEmpty()) {
			return;
		}
		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		Listing listing = program.getListing();
		FunctionManager functions = program.getFunctionManager();
		Map<Address, Integer> common = new HashMap<>();
		for (Address entry : entries.values()) {
			Branch branch = branch(program, disassembler, entry, MAX_ENTRY_LENGTH);
			if (branch != null && !entries.containsValue(branch.target())) {
				common.merge(branch.target(), 1, Integer::sum);
			}
		}
		for (Map.Entry<Address, Integer> c : common.entrySet()) {
			if (c.getValue() > 1 && functions.getFunctionAt(c.getKey()) == null) {
				manager.disassemble(c.getKey());
				manager.createFunction(c.getKey(), false);
			}
		}
		Set<Address> created = new HashSet<>();
		for (Map.Entry<Address, Address> e : entries.entrySet()) {
			E200Data.label(program, e.getKey(),
				"INTC_vector_" + e.getKey().subtract(first) / 4, SourceType.ANALYSIS);
			if (listing.getInstructionAt(e.getKey()) == null) {
				manager.disassemble(e.getKey());
			}
			if (functions.getFunctionAt(e.getValue()) == null && created.add(e.getValue())) {
				manager.createFunction(e.getValue(), false);
			}
		}
		Msg.info(E200Analyzer.class, "Hardware interrupt vectors at " + first + ": " +
			entries.size() + " in use");
	}
}
