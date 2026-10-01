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

import ghidra.app.util.PseudoDisassembler;
import ghidra.app.util.PseudoInstruction;
import ghidra.program.model.address.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.symbol.FlowType;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Finds functions that nothing calls or references directly and that do not start with a
 * stack frame, such as getters, table lookup routines and small helpers reached only
 * through tables that analysis cannot follow (part of {@link E200Functions}). Flow
 * analysis never reaches them and the function start patterns look for prologues, so they
 * stay undefined bytes between functions, or instructions of no function where a pointer in
 * data leads to them.
 * <p>
 * A gap of undefined bytes and instructions of no function directly after a function's return
 * or unconditional branch becomes functions only when all of it is code: the gap, apart from
 * {@code se_nop} and erased padding, must be covered exactly by subroutines that
 * <ul>
 * <li>decode completely and end in returns or branches on every path,</li>
 * <li>stay inside the gap, except for calls and branches to existing instructions,</li>
 * <li>agree with the instructions already in the gap,</li>
 * <li>have at least {@link #MIN_INSTRUCTIONS} instructions, and</li>
 * <li>contain no {@code se_illegal}, and none of the unusual instructions below unless the
 * program's code already uses that instruction: LSP and SPE vector instructions, system
 * and interrupt returns, TLB, MPU, DCR, cache locking, decorated storage and string
 * instructions.</li>
 * </ul>
 * Data rarely decodes that way, so tables, strings and constants between functions stay
 * data. Each subroutine becomes a function with an analysis bookmark.
 */
final class E200CodeGaps {

	static final String BOOKMARK_CATEGORY = "PowerPC e200 Functions";

	private static final int MIN_INSTRUCTIONS = 2;
	/** An unusual instruction is accepted when the program's code already uses it this often. */
	private static final int COMMON_USES = 5;
	private static final int SE_NOP = 0x4400;
	private static final int ERASED = 0xffff;

	/** Instructions typical of data decoded as VLE, or of code that is never a plain leaf. */
	private static final Set<String> NEVER = Set.of("se_illegal", "illegal");
	private static final String[] UNUSUAL_PREFIXES = { "z", "ev", "efd", "tlb", "mpu", "dcbl",
		"icbl", "e_ldmv", "e_stmv", "lsw", "stsw", "mfdcr", "mtdcr", "wait", "e_sc", "se_sc",
		"sc", "tw", "se_rf", "rf", "mtmsr", "mfmsr", "wrtee" };
	private static final Set<String> DECORATED = Set.of("lbdx", "lhdx", "lwdx", "stbdx",
		"sthdx", "stwdx", "lbdcbx", "lhdcbx", "lwdcbx", "stbdcbx", "sthdcbx", "stwdcbx");

	private E200CodeGaps() {
	}

	/**
	 * Disassembles the subroutines in the gaps after the functions in {@code set} and creates
	 * their functions; returns how many.
	 */
	static int findFunctions(Program program, AddressSetView set, TaskMonitor monitor)
			throws CancelledException {
		Listing listing = program.getListing();
		AddressSetView executable = E200Analyzer.executableMemory(program);
		Set<Address> gaps = new TreeSet<>();
		for (Function function : program.getFunctionManager().getFunctions(set, true)) {
			for (AddressRange range : function.getBody()) {
				Address next = range.getMaxAddress().next();
				if (next != null && executable.contains(next) && isFree(listing, next)) {
					gaps.add(next);
				}
			}
		}
		if (gaps.isEmpty()) {
			return 0;
		}
		Map<String, Integer> uses = mnemonicUses(program, monitor);
		PseudoDisassembler disassembler = new PseudoDisassembler(program);
		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		int found = 0;
		for (Address gap : gaps) {
			monitor.checkCancelled();
			List<Address> entries = findSubroutines(program, disassembler, uses, gap, executable);
			for (Address entry : entries) {
				manager.disassemble(entry);
				manager.createFunction(entry, false);
				program.getBookmarkManager()
						.setBookmark(entry, BookmarkType.ANALYSIS, BOOKMARK_CATEGORY,
							"Function in a gap between functions");
				found++;
			}
		}
		if (found > 0) {
			Msg.info(E200Analyzer.class, "Found " + found + " functions in gaps between functions");
		}
		return found;
	}

	private static Map<String, Integer> mnemonicUses(Program program, TaskMonitor monitor)
			throws CancelledException {
		Map<String, Integer> uses = new HashMap<>();
		for (Instruction instruction : program.getListing().getInstructions(true)) {
			monitor.checkCancelled();
			uses.merge(instruction.getMnemonicString(), 1, Integer::sum);
		}
		return uses;
	}

	/**
	 * The entry points of the subroutines that cover the gap starting at {@code start}, or an
	 * empty list if the gap is not all code.
	 */
	static List<Address> findSubroutines(Program program, PseudoDisassembler disassembler,
			Map<String, Integer> uses, Address start, AddressSetView executable) {
		Listing listing = program.getListing();
		Memory memory = program.getMemory();
		if ((start.getOffset() & 1) != 0 || !endsFlow(listing, start)) {
			return List.of();
		}
		AddressRange gap = freeRange(listing, start, executable);
		if (gap == null) {
			return List.of();
		}
		Address end = gap.getMaxAddress();
		TreeMap<Address, Integer> code = new TreeMap<>();
		List<Address> entries = new ArrayList<>();
		Address a = start;
		while (a != null && a.compareTo(end) <= 0) {
			Integer length = code.get(a);
			if (length != null) {
				a = next(a, length, end);
				continue;
			}
			int halfword;
			try {
				halfword = memory.getShort(a) & 0xffff;
			}
			catch (MemoryAccessException e) {
				return List.of();
			}
			if (halfword == SE_NOP || halfword == ERASED) {
				a = next(a, 2, end);
				continue;
			}
			// uncovered bytes that are not padding: the next subroutine must start here
			Map<Address, Integer> body =
				followSubroutine(listing, disassembler, uses, a, gap, code.keySet());
			if (body == null) {
				return List.of();
			}
			code.putAll(body);
			entries.add(a);
		}
		if (entries.isEmpty() ||
			!internalTargetsAreInstructions(listing, disassembler, code, gap)) {
			return List.of();
		}
		return entries;
	}

	/** Whether the code unit before {@code address} is a return or unconditional branch. */
	private static boolean endsFlow(Listing listing, Address address) {
		Address previous = address.previous();
		if (previous == null) {
			return false;
		}
		Instruction instruction = listing.getInstructionContaining(previous);
		if (instruction == null) {
			return false;
		}
		FlowType flow = instruction.getFlowType();
		// not a computed jump: a switch table may follow
		return !flow.hasFallthrough() && !flow.isComputed() &&
			(flow.isTerminal() || flow.isJump());
	}

	/** Whether the address is undefined, or in an instruction of no function. */
	private static boolean isFree(Listing listing, Address address) {
		if (listing.isUndefined(address, address)) {
			return true;
		}
		Instruction instruction = listing.getInstructionContaining(address);
		return instruction != null && listing.getFunctionContaining(address) == null;
	}

	/**
	 * The undefined bytes and instructions of no function from {@code start} to the next data,
	 * instruction of a function or end of the memory block.
	 */
	private static AddressRange freeRange(Listing listing, Address start,
			AddressSetView executable) {
		AddressRange block = executable.getRangeContaining(start);
		if (block == null) {
			return null;
		}
		Address limit = block.getMaxAddress();
		CodeUnit following = listing.getDefinedCodeUnitAfter(start);
		while (following != null && following.getMinAddress().compareTo(limit) <= 0 &&
			following instanceof Instruction &&
			listing.getFunctionContaining(following.getMinAddress()) == null) {
			following = listing.getDefinedCodeUnitAfter(following.getMaxAddress());
		}
		if (following != null && following.getMinAddress().compareTo(limit) <= 0) {
			limit = following.getMinAddress().previous();
		}
		return limit == null || limit.compareTo(start) < 0 ? null
				: new AddressRangeImpl(start, limit);
	}

	private static Address next(Address a, int length, Address end) {
		try {
			Address n = a.addNoWrap(length);
			return n.compareTo(end) <= 0 ? n : null;
		}
		catch (AddressOverflowException e) {
			return null;
		}
	}

	/**
	 * Follows every path from {@code entry} and returns the instructions (address to length),
	 * or null if a path leaves the gap other than to existing code, does not decode, uses an
	 * unusual instruction, or does not end in a return or branch.
	 */
	private static Map<Address, Integer> followSubroutine(Listing listing,
			PseudoDisassembler disassembler, Map<String, Integer> uses, Address entry,
			AddressRange gap, Set<Address> covered) {
		Map<Address, Integer> body = new HashMap<>();
		Deque<Address> todo = new ArrayDeque<>();
		todo.push(entry);
		boolean ends = false;
		while (!todo.isEmpty()) {
			Address a = todo.pop();
			if (body.containsKey(a) || covered.contains(a)) {
				continue;
			}
			if (!gap.contains(a)) {
				return null;
			}
			PseudoInstruction instruction;
			try {
				instruction = disassembler.disassemble(a);
			}
			catch (Exception e) {
				return null;
			}
			if (instruction == null || !gap.contains(a.add(instruction.getLength() - 1)) ||
				!plausible(instruction.getMnemonicString(), uses) ||
				!agrees(listing, a, instruction.getLength())) {
				return null;
			}
			body.put(a, instruction.getLength());
			FlowType flow = instruction.getFlowType();
			for (Address target : instruction.getFlows()) {
				if (gap.contains(target)) {
					if (!flow.isCall()) {
						todo.push(target);
					}
				}
				else if (listing.getInstructionAt(target) == null) {
					return null; // into undefined bytes or the middle of an instruction
				}
			}
			if (flow.hasFallthrough()) {
				todo.push(a.add(instruction.getLength()));
			}
			else {
				ends = true;
			}
		}
		return ends && body.size() >= MIN_INSTRUCTIONS ? body : null;
	}

	/** Whether the listing has no instruction that overlaps {@code a} differently. */
	private static boolean agrees(Listing listing, Address a, int length) {
		Instruction first = listing.getInstructionContaining(a);
		Instruction last = listing.getInstructionContaining(a.add(length - 1));
		if (first == null && last == null) {
			return true;
		}
		return first != null && first == last && first.getAddress().equals(a) &&
			first.getLength() == length;
	}

	private static boolean plausible(String mnemonic, Map<String, Integer> uses) {
		if (NEVER.contains(mnemonic)) {
			return false;
		}
		boolean unusual = DECORATED.contains(mnemonic);
		for (String prefix : UNUSUAL_PREFIXES) {
			unusual |= mnemonic.startsWith(prefix);
		}
		return !unusual || uses.getOrDefault(mnemonic, 0) >= COMMON_USES;
	}

	/** Branches and calls into the gap must land on the start of a covered instruction. */
	private static boolean internalTargetsAreInstructions(Listing listing,
			PseudoDisassembler disassembler, Map<Address, Integer> code, AddressRange gap) {
		for (Address a : code.keySet()) {
			PseudoInstruction instruction;
			try {
				instruction = disassembler.disassemble(a);
			}
			catch (Exception e) {
				return false;
			}
			for (Address target : instruction.getFlows()) {
				if (gap.contains(target) && !code.containsKey(target)) {
					return false;
				}
			}
		}
		return true;
	}
}
