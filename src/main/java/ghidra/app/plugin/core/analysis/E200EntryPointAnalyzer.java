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

import ghidra.app.services.*;
import ghidra.app.util.PseudoDisassembler;
import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.*;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

/**
 * Finds the entry points of MPC57xx flash images for the NXP e200z4 VLE language
 * ({@code PowerPC:BE:32:VLE-e200}): the reset vectors in boot headers and the interrupt
 * vectors. A raw flash image has no other entry points, and startup code usually reaches the
 * interrupt setup only through values that analysis cannot follow.
 * <ul>
 * <li>Boot headers: the boot assist flash looks for a boot header at the start of flash
 * blocks. Its first word holds the boot identifier 0x5A in bits 8-15 ({@code 0x005A....}),
 * and the words at offsets 0x10-0x1C hold the reset vectors of the cores, or 0 for a core
 * that is not started. Checked at the start of each memory block and every 16 KB.</li>
 * <li>Interrupt vector tables: the e200z4 has fixed vector offsets from IVPR, 16 bytes
 * apart, and each vector in use holds an {@code e_b} to its handler. A table is taken to be
 * at least {@link #MIN_VECTORS} such vectors from a 256-byte boundary. The vectors are
 * labeled ({@code IVOR4_ExternalInput}, ...) and the handlers become functions.</li>
 * </ul>
 */
public class E200EntryPointAnalyzer extends AbstractAnalyzer {

	private static final String NAME = "PowerPC e200 Entry Points";
	private static final String DESCRIPTION =
		"Finds the entry points of MPC57xx flash images: the reset vectors in boot headers\n" +
			"(a word 0x005A.... at the start of a block or a 16 KB boundary) and interrupt vector\n" +
			"tables (e_b instructions 16 bytes apart), and disassembles them as functions.";

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

	public E200EntryPointAnalyzer() {
		super(NAME, DESCRIPTION, AnalyzerType.BYTE_ANALYZER);
		setPriority(AnalysisPriority.FORMAT_ANALYSIS);
		setDefaultEnablement(true);
		setSupportsOneTimeAnalysis();
	}

	@Override
	public boolean canAnalyze(Program program) {
		return E200AddressAnalyzer.LANGUAGE_ID.equals(program.getLanguageID().getIdAsString());
	}

	@Override
	public boolean added(Program program, AddressSetView set, TaskMonitor monitor,
			MessageLog log) throws CancelledException {
		for (MemoryBlock block : program.getMemory().getBlocks()) {
			monitor.checkCancelled();
			if (block.isInitialized() && set.intersects(block.getStart(), block.getEnd())) {
				findBootHeaders(program, block, set);
			}
		}
		for (AddressRange range : E200AddressAnalyzer.executableMemory(program).intersect(set)) {
			findVectorTables(program, range, monitor);
		}
		return true;
	}

	// ---- Boot headers -----------------------------------------------------------------------

	private void findBootHeaders(Program program, MemoryBlock block, AddressSetView set) {
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
			if (header.compareTo(last) <= 0 && set.contains(header)) {
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

		try {
			program.getListing().createData(header, bootHeaderType(program));
		}
		catch (CodeUnitInsertionException e) {
			// something is already defined there
		}
		label(program, header, "boot_header");

		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		for (int i = 0; i < VECTOR_COUNT; i++) {
			Address vector = vectors.get(i);
			if (vector == null || vectors.indexOf(vector) != i) {
				continue; // no vector, or the same as an earlier core's
			}
			label(program, vector, distinct.size() == 1 ? "reset" : "reset_" + i);
			program.getSymbolTable().addExternalEntryPoint(vector);
			manager.disassemble(vector);
			manager.createFunction(vector, false);
			Msg.info(this, "Boot header at " + header + ": reset vector " + vector);
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

	private void findVectorTables(Program program, AddressRange range, TaskMonitor monitor)
			throws CancelledException {
		Memory memory = program.getMemory();
		long start = (range.getMinAddress().getOffset() + TABLE_ALIGNMENT - 1) & -TABLE_ALIGNMENT;
		long end = range.getMaxAddress().getOffset();
		for (long offset = start; offset + MIN_VECTORS * VECTOR_SPACING - 1 <= end;
				offset += TABLE_ALIGNMENT) {
			monitor.checkCancelled();
			Address table = range.getMinAddress().getNewAddress(offset);
			if (branchTarget(memory, table, -VECTOR_SPACING) != null) {
				continue; // inside a longer run of branches
			}
			List<Address> handlers = new ArrayList<>();
			for (int i = 0; i <= IVORS.length; i++) {
				Address handler = branchTarget(memory, table, i * VECTOR_SPACING);
				if (handler == null) {
					break;
				}
				handlers.add(handler);
			}
			// more branches than there are vectors: some other kind of table
			if (handlers.size() >= MIN_VECTORS && handlers.size() <= IVORS.length) {
				markVectorTable(program, table, handlers);
			}
		}
	}

	/**
	 * The target of the {@code e_b} (not {@code e_bl}) at {@code table + offset}, if it is in
	 * initialized memory. {@code e_b} is opcode 30 with bit 6 and LK clear; the displacement
	 * is bits 7-30.
	 */
	private static Address branchTarget(Memory memory, Address table, int offset) {
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

	private void markVectorTable(Program program, Address table, List<Address> handlers) {
		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		Address tableEnd = table.add(handlers.size() * VECTOR_SPACING - 1);
		for (int i = 0; i < handlers.size(); i++) {
			Address vector = table.add(i * VECTOR_SPACING);
			label(program, vector, IVORS[i]);
			manager.disassemble(vector);
			Address handler = handlers.get(i);
			if (handler.compareTo(table) < 0 || handler.compareTo(tableEnd) > 0) {
				manager.createFunction(handler, false);
			}
		}
		Msg.info(this, "Interrupt vector table at " + table + ": " + handlers.size() +
			" vectors");
	}

	private static void label(Program program, Address address, String name) {
		SymbolTable symbols = program.getSymbolTable();
		Symbol primary = symbols.getPrimarySymbol(address);
		if (primary != null && primary.getSource() != SourceType.DEFAULT) {
			return;
		}
		try {
			symbols.createLabel(address, name, SourceType.ANALYSIS);
		}
		catch (InvalidInputException e) {
			// not a valid name
		}
	}
}
