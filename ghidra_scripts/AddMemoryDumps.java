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
// Adds the MPC5746R memory dumps in a folder to the current program, each at the address
// range its file name ends with, as in sram_40000000-4003FFFF.bin.
//
// RAM dumps become read/write blocks (local instruction memory also executable), the data
// flash at 0x00800000 a read/write block, and anything else, such as code flash, a
// read/write/execute block as the Raw Binary loader creates it. A dump over uninitialized
// blocks, such as the RAM blocks the e200 analysis adds, fills them and keeps their data;
// a dump over initialized memory is skipped. Run analysis afterwards (again).
//
// Headless: -postScript AddMemoryDumps.java <folder>
//@category PowerPC e200
import java.io.*;
import java.nio.file.Files;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ghidra.app.script.GhidraScript;
import ghidra.program.database.mem.FileBytes;
import ghidra.program.model.address.*;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;

public class AddMemoryDumps extends GhidraScript {

	private static final Pattern RANGE =
		Pattern.compile("([0-9A-Fa-f]{8})-([0-9A-Fa-f]{8})\\.bin$");

	/** MPC5746R data memory: SRAM and the cores' local data memories. */
	private static final long[][] DATA_RAM = { { 0x4000_0000L, 0x4003_FFFFL },
		{ 0x5080_0000L, 0x5080_7FFFL }, { 0x5180_0000L, 0x5180_7FFFL } };

	/** MPC5746R local instruction memories. */
	private static final long[][] INSTRUCTION_RAM =
		{ { 0x5000_0000L, 0x5000_3FFFL }, { 0x5100_0000L, 0x5100_3FFFL } };

	/** MPC5746R data flash, used for EEPROM emulation. */
	private static final long[][] DATA_FLASH = { { 0x0080_0000L, 0x0083_FFFFL } };

	@Override
	protected void run() throws Exception {
		String[] args = getScriptArgs();
		File folder = args.length > 0 ? new File(args[0])
				: askDirectory("Folder with memory dumps", "Add dumps");
		File[] files = folder.listFiles((dir, name) -> RANGE.matcher(name).find());
		if (files == null || files.length == 0) {
			printerr("No files named like sram_40000000-4003FFFF.bin in " + folder);
			return;
		}
		Arrays.sort(files);
		for (File file : files) {
			Matcher m = RANGE.matcher(file.getName());
			m.find();
			long start = Long.parseLong(m.group(1), 16);
			long end = Long.parseLong(m.group(2), 16);
			if (end < start || end - start + 1 != file.length()) {
				printerr("Skipping " + file.getName() + ": its size is not that of " +
					m.group(1) + "-" + m.group(2));
				continue;
			}
			addDump(file, toAddr(start), toAddr(end));
		}
	}

	private void addDump(File file, Address first, Address last) throws Exception {
		Memory memory = currentProgram.getMemory();
		for (MemoryBlock block : memory.getBlocks()) {
			if (block.isInitialized() && block.getStart().compareTo(last) <= 0 &&
				block.getEnd().compareTo(first) >= 0) {
				println("Skipping " + file.getName() + ": " + block.getName() +
					" is already there");
				return;
			}
		}
		String name = file.getName().substring(0, file.getName().length() - 4);
		byte[] bytes = Files.readAllBytes(file.toPath());
		List<MemoryBlock> added = new ArrayList<>();

		// uninitialized blocks in the way: split them at the dump's bounds and fill them
		Set<String> names = new HashSet<>();
		for (MemoryBlock block : memory.getBlocks()) {
			names.add(block.getName());
		}
		split(first);
		if (last.getOffset() < last.getAddressSpace().getMaxAddress().getOffset()) {
			split(last.next());
		}
		for (MemoryBlock block : memory.getBlocks()) {
			if (block.getStart().compareTo(first) >= 0 && block.getEnd().compareTo(last) <= 0) {
				MemoryBlock filled = memory.convertToInitialized(block, (byte) 0);
				memory.setBytes(filled.getStart(), bytes,
					(int) filled.getStart().subtract(first), (int) filled.getSize());
				added.add(filled);
			}
		}
		// the rest from the file
		AddressSet unmapped = new AddressSet(first, last).subtract(memory);
		if (!unmapped.isEmpty()) {
			FileBytes fileBytes;
			try (InputStream in = new FileInputStream(file)) {
				fileBytes = memory.createFileBytes(file.getName(), 0, file.length(), in, monitor);
			}
			for (AddressRange range : unmapped) {
				added.add(memory.createInitializedBlock(name, range.getMinAddress(), fileBytes,
					range.getMinAddress().subtract(first), range.getLength(), false));
			}
		}

		long start = first.getOffset();
		long end = last.getOffset();
		boolean dataRam = within(start, end, DATA_RAM);
		boolean dataFlash = within(start, end, DATA_FLASH);
		boolean execute = within(start, end, INSTRUCTION_RAM) || (!dataRam && !dataFlash);
		added.sort(Comparator.comparing(MemoryBlock::getStart));
		for (int i = 0; i < added.size(); i++) {
			MemoryBlock block = added.get(i);
			block.setName(i == 0 ? name : name + "_" + i);
			block.setPermissions(true, true, execute);
			block.setComment("Dump " + file.getName());
		}
		renameSplitBlocks(names);
		println("Added " + name + " at " + first + "-" + last + (execute ? " (executable)" : ""));
	}

	/** Splits the block containing an address there, unless the address starts it. */
	private void split(Address address) throws Exception {
		MemoryBlock block = currentProgram.getMemory().getBlock(address);
		if (block != null && !block.getStart().equals(address)) {
			currentProgram.getMemory().split(block, address);
		}
	}

	/**
	 * Names the parts that splitting left outside a dump, which Ghidra names ...split, after
	 * their block and address.
	 */
	private void renameSplitBlocks(Set<String> names) throws Exception {
		for (MemoryBlock block : currentProgram.getMemory().getBlocks()) {
			String name = block.getName();
			if (name.endsWith(".split") && !names.contains(name)) {
				block.setName(name.substring(0, name.indexOf(".split")) + "_" + block.getStart());
			}
		}
	}

	private static boolean within(long start, long end, long[][] regions) {
		for (long[] region : regions) {
			if (start >= region[0] && end <= region[1]) {
				return true;
			}
		}
		return false;
	}
}
