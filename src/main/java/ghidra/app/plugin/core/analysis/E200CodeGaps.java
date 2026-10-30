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
import ghidra.program.model.address.*;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.*;
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
 * <li>have at least {@link #MIN_INSTRUCTIONS} instructions, or are a lone {@code se_blr}, an
 * empty function between the others, and</li>
 * <li>contain no {@code se_illegal}, and none of the unusual instructions below unless the
 * program's code already uses that instruction: LSP and SPE vector instructions, system
 * and interrupt returns, TLB, MPU, DCR, cache locking, decorated storage and string
 * instructions.</li>
 * </ul>
 * Data rarely decodes that way, so tables, strings and constants between functions stay
 * data. Each subroutine becomes a function with an analysis bookmark. The padding a gap
 * begins with, {@code se_nop} or {@code se_or rX,rX}, is disassembled.
 * <p>
 * Two kinds of tables lead to code too: tables of handlers, pointers in a column of function
 * entry points (see {@link #findPointedFunctions}), and branch tables, runs of {@code e_b}
 * right after code that does not fall through, which a computed jump selects an entry of
 * (see {@link #findBranchTables}).
 */
final class E200CodeGaps {

	static final String BOOKMARK_CATEGORY = "PowerPC e200 Functions";

	private static final int MIN_INSTRUCTIONS = 2;
	/** An unusual instruction is accepted when the program's code already uses it this often. */
	private static final int COMMON_USES = 5;
	private static final int SE_NOP = 0x4400;
	private static final int SE_BLR = 0x0004;
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
	static List<Address> findFunctions(Program program, AddressSetView set, TaskMonitor monitor)
			throws CancelledException {
		Listing listing = program.getListing();
		AddressSetView executable = E200Code.executableMemory(program);
		Set<Address> gaps = new TreeSet<>();
		for (Function function : program.getFunctionManager().getFunctions(set, true)) {
			for (AddressRange range : function.getBody()) {
				Address next = range.getMaxAddress().next();
				if (next != null && executable.contains(next) && isFree(listing, next)) {
					gaps.add(next);
				}
			}
		}
		List<Address> found = new ArrayList<>();
		if (gaps.isEmpty()) {
			return found;
		}
		Map<String, Integer> uses = mnemonicUses(program, monitor);
		PseudoDisassembler disassembler = new PseudoDisassembler(program);
		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		int padding = 0;
		for (Address gap : gaps) {
			monitor.checkCancelled();
			padding += disassemblePadding(program, gap, executable);
			List<Address> entries = findSubroutines(program, disassembler, uses, gap, executable);
			for (Address entry : entries) {
				manager.disassemble(entry);
				manager.createFunction(entry, false);
				program.getBookmarkManager()
						.setBookmark(entry, BookmarkType.ANALYSIS, BOOKMARK_CATEGORY,
							"Function in a gap between functions");
				found.add(entry);
			}
		}
		if (!found.isEmpty()) {
			Msg.info(E200Analyzer.class,
				"Found " + found.size() + " functions in gaps between functions");
		}
		if (padding > 0) {
			Msg.info(E200Analyzer.class,
				"Disassembled " + padding + " no-op instructions of padding after functions");
		}
		return found;
	}

	/**
	 * Disassembles the {@code se_nop} and {@code se_or rX,rX} that the gap starting at
	 * {@code start}, after a return or unconditional branch, begins with, where a function or
	 * data follows them: the padding compilers put between functions, which nothing executes.
	 * Returns how many.
	 */
	private static int disassemblePadding(Program program, Address start,
			AddressSetView executable) {
		Listing listing = program.getListing();
		if ((start.getOffset() & 1) != 0 || !endsFlow(listing, start)) {
			return 0;
		}
		AddressRange gap = freeRange(listing, start, executable);
		if (gap == null) {
			return 0;
		}
		Memory memory = program.getMemory();
		Address end = null;
		int count = 0;
		for (Address a = start; a != null && a.compareTo(gap.getMaxAddress()) < 0;
				a = next(a, 2, gap.getMaxAddress())) {
			try {
				int halfword = memory.getShort(a) & 0xffff;
				// se_or rX,rX does nothing, as se_nop (se_or r0,r0): the fill some compilers use
				if ((halfword & 0xff00) != SE_NOP || (halfword >> 4 & 0xf) != (halfword & 0xf) ||
					!listing.isUndefined(a, a.add(1))) {
					break;
				}
			}
			catch (MemoryAccessException | AddressOutOfBoundsException e) {
				break;
			}
			end = a.add(1);
			count++;
		}
		// only once what follows is settled, a function or data: code that a later function
		// takes in may still be found after the padding
		Address after = end == null ? null : end.next();
		if (after == null || program.getFunctionManager().getFunctionAt(after) == null &&
			listing.getDefinedDataAt(after) == null) {
			return 0;
		}
		AddressSet nops = new AddressSet(start, end);
		new DisassembleCommand(nops, nops, true).applyTo(program);
		return count;
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
	private static List<Address> findSubroutines(Program program,
			PseudoDisassembler disassembler, Map<String, Integer> uses, Address start,
			AddressSetView executable) {
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
				followSubroutine(listing, disassembler, uses, a, gap, code.keySet(), 1, false);
			if (body == null || body.size() < MIN_INSTRUCTIONS && !emptyFunction(memory, a)) {
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

	/** Whether the instruction at {@code address} is a lone {@code se_blr}: an empty function */
	private static boolean emptyFunction(Memory memory, Address address) {
		try {
			return (memory.getShort(address) & 0xffff) == SE_BLR;
		}
		catch (MemoryAccessException e) {
			return false;
		}
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
		return followSubroutine(listing, disassembler, uses, entry, gap, covered,
			MIN_INSTRUCTIONS, false);
	}

	/**
	 * As above, with at least {@code minInstructions}; where the subroutine must be
	 * {@code compiled} code, also null if it writes a register that the EABI has functions
	 * keep (r2, r13, r14-r31) without a stack frame to save it in. Hand-written routines
	 * after the code of a function, as self-tests of the core, use those registers freely.
	 */
	private static Map<Address, Integer> followSubroutine(Listing listing,
			PseudoDisassembler disassembler, Map<String, Integer> uses, Address entry,
			AddressRange gap, Set<Address> covered, int minInstructions, boolean compiled) {
		Map<Address, Integer> body = new HashMap<>();
		Deque<Address> todo = new ArrayDeque<>();
		todo.push(entry);
		boolean ends = false;
		boolean frame = false; // writes the stack pointer: has a frame to save registers in
		boolean keeps = false; // writes a register that a function must keep
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
			for (Object result : instruction.getResultObjects()) {
				if (result instanceof Register r && r.getName().matches("r[0-9]+")) {
					int n = Integer.parseInt(r.getName().substring(1));
					frame |= n == 1;
					keeps |= n == 2 || n >= 13;
				}
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
		// compiled code keeps r2, r13 and r14-r31 (the EABI's non-volatile registers): a
		// subroutine that writes one without a stack frame to save it in is data
		return ends && body.size() >= minInstructions && !(compiled && keeps && !frame) ? body
				: null;
	}

	/** How far around a pointer the words of its table are looked at, in bytes */
	private static final int REACH = 32;
	/** How close to a handler a pointer target that is no function may lie, in bytes */
	private static final int NEAR = 8;
	private static final int CHUNK = 0x10000;

	/**
	 * Creates functions at the code that pointers in tables of handlers point to: an aligned
	 * word of initialized memory whose value is an even address in executable memory outside
	 * every function, where the bytes decode as a complete subroutine, when the word is in a
	 * column of function entry points, at one stride (4 to {@link #REACH} bytes, as a field
	 * of a table of structures is; see {@link #column}): between two entries, at the end of a
	 * column of two, or, in an array of pointers, next to one entry at an end of the array,
	 * for a subroutine of more than one instruction or one that directly follows the return
	 * or branch that ends a function, as compiled code places functions. A pointer target
	 * within {@link #NEAR} bytes of the code or inside it that is no function, instruction or
	 * candidate says the bytes are data: the values of a table that a table of structures
	 * points to one by one decode as code too; so does code that writes a register compiled
	 * code keeps without a stack frame. An empty handler, one return, matches no start
	 * pattern, and the gap rule above takes it only in a gap that is all code; the table says
	 * it is a function. Returns how many were created; {@code scheduled} are the entry points
	 * of the functions the gap rule has just scheduled, not created yet, which need no table.
	 */
	static int findPointedFunctions(Program program, Collection<Address> scheduled,
			TaskMonitor monitor) throws CancelledException {
		Listing listing = program.getListing();
		Memory memory = program.getMemory();
		FunctionManager functions = program.getFunctionManager();
		AddressSetView executable = E200Code.executableMemory(program);
		AddressSpace space = program.getAddressFactory().getDefaultAddressSpace();
		// the free code that words point to, by the words; then the candidates with the
		// strength of their column: 2 for a column of function entry points, 1 for an end
		Map<Address, List<Address>> words = new TreeMap<>();
		Map<Address, Integer> candidates = new TreeMap<>();
		byte[] bytes = new byte[CHUNK + 2 * REACH];
		for (int pass = 0; pass < 2; pass++) {
			for (MemoryBlock block : memory.getBlocks()) {
				if (!block.isInitialized() || block.isVolatile() ||
					!block.getStart().getAddressSpace().equals(space)) {
					continue;
				}
				Address start = block.getStart();
				long size = block.getSize();
				for (long offset = 0; offset + 3 < size; offset += CHUNK) {
					monitor.checkCancelled();
					long from = Math.max(0, offset - REACH);
					int length = (int) Math.min(bytes.length, size - from);
					try {
						memory.getBytes(start.add(from), bytes, 0, length);
					}
					catch (MemoryAccessException | AddressOutOfBoundsException e) {
						break;
					}
					int first = (int) (offset - from);
					int last = Math.min(length, first + CHUNK);
					for (int i = first; i + 3 < last; i += 4) {
						long value = word(bytes, i);
						if ((value & 1) != 0 || value == 0 ||
							!executable.contains(space.getAddress(value))) {
							continue;
						}
						Address target = space.getAddress(value);
						if (pass == 0) {
							if (functions.getFunctionContaining(target) == null &&
								!scheduled.contains(target) && isFree(listing, target)) {
								words.computeIfAbsent(target, t -> new ArrayList<>(1))
										.add(start.add(from + i));
							}
							continue;
						}
						if (!words.containsKey(target)) {
							continue;
						}
						int column =
							column(functions, memory, space, words.keySet(), bytes, i, length);
						if (column > 0) {
							candidates.merge(target, column, Math::max);
						}
					}
				}
			}
		}
		if (candidates.isEmpty()) {
			return 0;
		}
		Map<String, Integer> uses = mnemonicUses(program, monitor);
		PseudoDisassembler disassembler = new PseudoDisassembler(program);
		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		TreeSet<Address> pointed = new TreeSet<>(E200Data.pointerTargets(program));
		int found = 0;
		for (Map.Entry<Address, Integer> candidate : candidates.entrySet()) {
			monitor.checkCancelled();
			Address entry = candidate.getKey();
			AddressRange gap = freeRange(listing, entry, executable);
			Map<Address, Integer> body = gap == null ? null
					: followSubroutine(listing, disassembler, uses, entry, gap, Set.of(), 1,
						true);
			if (body == null ||
				body.size() < MIN_INSTRUCTIONS && candidate.getValue() < 2 &&
					!afterFunction(listing, entry) ||
				dataNear(listing, functions, pointed, candidates.keySet(), entry, body)) {
				continue;
			}
			manager.disassemble(entry);
			manager.createFunction(entry, false);
			program.getBookmarkManager()
					.setBookmark(entry, BookmarkType.ANALYSIS, BOOKMARK_CATEGORY,
						"Function that a table of handlers points to");
			found++;
		}
		if (found > 0) {
			Msg.info(E200Analyzer.class, "Found " + found + " functions that tables point to");
		}
		return found;
	}

	/** Fewest branches taken as a branch table */
	private static final int MIN_BRANCHES = 2;

	/**
	 * Disassembles the branch tables that computed jumps select an entry of, and makes
	 * functions of the code their entries branch to: a run of at least {@link #MIN_BRANCHES}
	 * {@code e_b} instructions in undefined bytes directly after an instruction that does not
	 * fall through, as the interrupt dispatch of an operating system adds four times a number
	 * to the address of the table and returns to it ({@code se_mtlr}, {@code se_blr}). The
	 * targets must lie in executable memory outside the table and decode as code; those in a
	 * function stay in it. Returns how many functions were created.
	 */
	static int findBranchTables(Program program, TaskMonitor monitor) throws CancelledException {
		Listing listing = program.getListing();
		Memory memory = program.getMemory();
		FunctionManager functions = program.getFunctionManager();
		AddressSetView executable = E200Code.executableMemory(program);
		PseudoDisassembler disassembler = new PseudoDisassembler(program);
		AutoAnalysisManager manager = AutoAnalysisManager.getAnalysisManager(program);
		Set<Address> created = new HashSet<>();
		for (Instruction instruction : listing.getInstructions(executable, true)) {
			monitor.checkCancelled();
			Address next = instruction.getMaxAddress().next();
			if (instruction.hasFallthrough() || next == null ||
				listing.getUndefinedDataAt(next) == null) {
				continue;
			}
			List<Address> targets = new ArrayList<>();
			Address end = next;
			for (Address a = next; a != null; a = a.next()) {
				Address last;
				try {
					last = a.addNoWrap(3);
				}
				catch (AddressOverflowException e) {
					break;
				}
				Address target = executable.contains(a, last) && listing.isUndefined(a, last)
						? E200EntryPoints.branchTarget(memory, a, 0)
						: null;
				if (target == null || !executable.contains(target)) {
					break;
				}
				targets.add(target);
				end = last;
				a = last;
			}
			if (targets.size() < MIN_BRANCHES) {
				continue;
			}
			boolean code = true;
			for (Address target : targets) {
				code &= (target.compareTo(next) < 0 || target.compareTo(end) > 0) &&
					disassembler.isValidCode(target);
			}
			if (!code) {
				continue;
			}
			manager.disassemble(new AddressSet(next, end));
			for (Address target : targets) {
				if (functions.getFunctionContaining(target) == null && created.add(target)) {
					manager.createFunction(target, false);
					program.getBookmarkManager()
							.setBookmark(target, BookmarkType.ANALYSIS, BOOKMARK_CATEGORY,
								"Function that a branch table after a computed jump leads to");
				}
			}
		}
		if (!created.isEmpty()) {
			Msg.info(E200Analyzer.class,
				"Found " + created.size() + " functions that branch tables lead to");
		}
		return created.size();
	}

	private static long word(byte[] bytes, int i) {
		return (bytes[i] & 0xffL) << 24 | (bytes[i + 1] & 0xffL) << 16 |
			(bytes[i + 2] & 0xffL) << 8 | bytes[i + 3] & 0xffL;
	}

	/**
	 * How much the word at {@code i} of the buffer is in a column of function entry points,
	 * at the best stride: 2 where the words one stride before and after it both point to
	 * functions, or a word up to two strides before it and one up to two strides after it do
	 * and none of the four points elsewhere, or it ends a column of two (the two words before
	 * or after it at the stride point to functions, the word on the other side is no address,
	 * and the words between are not all pointers to code: a dense array of pointers is no
	 * column of a wider stride); 1 where, in an array of pointers (a stride of 4), one
	 * neighbour points to a function and the other is no address, at an end of the array; 0
	 * otherwise. Words that point to the same code count as entries next to a real one, as an
	 * array of the same default handler before the others; the other {@code candidates}, the
	 * free code that words point to, count as neither.
	 */
	private static int column(FunctionManager functions, Memory memory, AddressSpace space,
			Set<Address> candidates, byte[] bytes, int i, int length) {
		long value = word(bytes, i);
		int best = 0;
		for (int stride = 4; stride <= REACH; stride += 4) {
			// by k = -2, -1, 1, 2 strides: 1 a function entry, 2 the same code, 3 another
			// address, 0 no address or nothing
			int[] kinds = new int[5];
			boolean real = false;
			for (int k = -2; k <= 2; k++) {
				int at = i + k * stride;
				if (k == 0 || at < 0 || at + 3 >= length) {
					continue;
				}
				long word = word(bytes, at);
				if (entry(functions, space, word)) {
					kinds[k + 2] = 1;
					real = true;
				}
				else if (word == value) {
					kinds[k + 2] = 2;
				}
				else if (address(memory, space, word) &&
					!candidates.contains(space.getAddress(word))) {
					kinds[k + 2] = 3;
				}
			}
			if (!real) {
				continue;
			}
			boolean a = kinds[1] == 1 || kinds[1] == 2;
			boolean b = kinds[3] == 1 || kinds[3] == 2;
			boolean entryBefore = a || kinds[0] == 1 || kinds[0] == 2;
			boolean entryAfter = b || kinds[4] == 1 || kinds[4] == 2;
			boolean others = kinds[0] == 3 || kinds[1] == 3 || kinds[3] == 3 || kinds[4] == 3;
			if (a && b || entryBefore && entryAfter && !others) {
				return 2;
			}
			boolean twoBefore = a && (kinds[0] == 1 || kinds[0] == 2);
			boolean twoAfter = b && (kinds[4] == 1 || kinds[4] == 2);
			if (twoBefore &&
				end(functions, memory, space, candidates, bytes, i, stride, 1, length) ||
				twoAfter &&
					end(functions, memory, space, candidates, bytes, i, stride, -1, length)) {
				return 2; // the end of a column of two or more
			}
			if (stride == 4 && (kinds[1] == 1 && kinds[3] == 0 || kinds[3] == 1 && kinds[1] == 0)) {
				best = 1;
			}
		}
		return best;
	}

	/**
	 * Whether the column at a stride ends at the word at {@code i}: the word one stride on
	 * the {@code side} away from the column is no address, and the words between the column's
	 * two entries next to it are not all pointers to code, function entries or the free code
	 * that words point to (else the pointers are a dense array, which matches any stride; the
	 * other fields of a structure, other handlers among them, leave gaps)
	 */
	private static boolean end(FunctionManager functions, Memory memory, AddressSpace space,
			Set<Address> candidates, byte[] bytes, int i, int stride, int side, int length) {
		int beyond = i + side * stride;
		if (beyond < 0 || beyond + 3 >= length ||
			address(memory, space, word(bytes, beyond))) {
			return false;
		}
		boolean dense = stride > 4;
		for (int d = 4; d < stride && dense; d += 4) {
			int at = i - side * (stride + d);
			if (at < 0 || at + 3 >= length) {
				dense = false;
				break;
			}
			long word = word(bytes, at);
			dense = entry(functions, space, word) || word != 0 && (word & 1) == 0 &&
				word <= space.getMaxAddress().getOffset() &&
				candidates.contains(space.getAddress(word));
		}
		return !dense;
	}

	/**
	 * Whether the instruction that ends right before {@code entry} is the return or branch
	 * that ends a function, after which compiled code places the next function
	 */
	private static boolean afterFunction(Listing listing, Address entry) {
		Address before;
		try {
			before = entry.subtractNoWrap(1);
		}
		catch (AddressOverflowException e) {
			return false;
		}
		Instruction previous = listing.getInstructionContaining(before);
		return previous != null && previous.getMaxAddress().equals(before) &&
			!previous.hasFallthrough() &&
			listing.getFunctionContaining(previous.getAddress()) != null;
	}

	/** Whether a word is an even address in memory */
	private static boolean address(Memory memory, AddressSpace space, long word) {
		return word != 0 && word != 0xffffffffL && (word & 1) == 0 &&
			word <= space.getMaxAddress().getOffset() && memory.contains(space.getAddress(word));
	}

	/**
	 * Whether a pointer target that is no function, instruction or candidate lies within
	 * {@link #NEAR} bytes of the subroutine at {@code entry} (its instructions in
	 * {@code body}), or inside it: the bytes are the values of a table
	 */
	private static boolean dataNear(Listing listing, FunctionManager functions,
			TreeSet<Address> pointed, Set<Address> candidates, Address entry,
			Map<Address, Integer> body) {
		Address end = entry;
		for (Map.Entry<Address, Integer> e : body.entrySet()) {
			Address last = e.getKey().add(e.getValue() - 1);
			if (last.compareTo(end) > 0) {
				end = last;
			}
		}
		Address from = entry.getOffset() >= NEAR ? entry.subtract(NEAR) : entry;
		Address to;
		try {
			to = end.addNoWrap(NEAR);
		}
		catch (AddressOverflowException e) {
			to = end;
		}
		for (Address t : pointed.subSet(from, true, to, true)) {
			if (!t.equals(entry) && functions.getFunctionAt(t) == null &&
				listing.getInstructionAt(t) == null && !candidates.contains(t)) {
				return true;
			}
		}
		return false;
	}

	/** Whether a word is the entry point of a function */
	private static boolean entry(FunctionManager functions, AddressSpace space, long word) {
		return word != 0 && (word & 1) == 0 && word <= space.getMaxAddress().getOffset() &&
			functions.getFunctionAt(space.getAddress(word)) != null;
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
