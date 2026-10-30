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

import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.pcode.*;

/**
 * What code shows (shared by the steps of {@link E200Analyzer}): the executable memory of a
 * program, the registers that instructions read and write, and what the p-code of decompiled
 * functions says about values: the function a call goes to, the address a value is, the
 * type a value is cast to, and the stride of an index.
 */
final class E200Code {

	private E200Code() {
	}

	// ---- Instructions -------------------------------------------------------------------------

	/**
	 * Executable memory with initialized bytes, or all initialized memory if no block is
	 * marked executable.
	 */
	static AddressSetView executableMemory(Program program) {
		Memory memory = program.getMemory();
		AddressSet set = new AddressSet();
		for (MemoryBlock block : memory.getBlocks()) {
			if (block.isExecute() && block.isInitialized()) {
				set.add(block.getStart(), block.getEnd());
			}
		}
		return set.isEmpty() ? memory.getLoadedAndInitializedAddressSet() : set;
	}

	/** Whether an instruction writes a register or a register that contains it */
	static boolean writes(Instruction instruction, Register register) {
		for (Object result : instruction.getResultObjects()) {
			if (result instanceof Register r && r.contains(register)) {
				return true;
			}
		}
		return false;
	}

	/** Whether an instruction reads a register, or part of it */
	static boolean reads(Instruction instruction, Register register) {
		for (Object input : instruction.getInputObjects()) {
			if (input instanceof Register r && r.getBaseRegister().equals(register)) {
				return true;
			}
		}
		return false;
	}

	/** The size of the one load or store of an instruction, or 0 if it has none or several */
	static int accessSize(Instruction instruction) {
		if (instruction == null) {
			return 0;
		}
		int size = 0;
		for (PcodeOp op : instruction.getPcode()) {
			int s = switch (op.getOpcode()) {
				case PcodeOp.LOAD -> op.getOutput().getSize();
				case PcodeOp.STORE -> op.getInput(2).getSize();
				default -> 0;
			};
			if (s != 0) {
				if (size != 0) {
					return 0;
				}
				size = s;
			}
		}
		return size;
	}

	// ---- P-code -------------------------------------------------------------------------------

	/** The function a call goes to, past thunks, or null */
	static Function callee(FunctionManager functions, PcodeOp call) {
		Varnode target = call.getInput(0);
		if (target == null || !target.isAddress()) {
			return null;
		}
		Function f = functions.getFunctionAt(target.getAddress());
		if (f != null && f.isThunk()) {
			f = f.getThunkedFunction(true);
		}
		return f == null || f.isExternal() ? null : f;
	}

	/**
	 * The address of a global that a value is, as in {@code f(&g)} or
	 * {@code f((T *)0x40001234)}: the address of a symbol, or a constant that is an address in
	 * RAM or flash; null otherwise
	 */
	static Address addressOf(Program program, Varnode value, int depth) {
		if (value == null || depth > 3) {
			return null;
		}
		if (value.isConstant()) {
			if (value.getSize() != 4 || value.getOffset() == 0) {
				return null;
			}
			Address address = program.getAddressFactory()
					.getDefaultAddressSpace()
					.getTruncatedAddress(value.getOffset(), true);
			MemoryBlock block = program.getMemory().getBlock(address);
			return block == null || block.isVolatile() ? null : address;
		}
		PcodeOp def = value.getDef();
		if (def == null) {
			return null;
		}
		return switch (def.getOpcode()) {
			case PcodeOp.CAST, PcodeOp.COPY -> addressOf(program, def.getInput(0), depth + 1);
			// the address of a global, &DAT_...
			case PcodeOp.PTRSUB -> def.getInput(0).isConstant() &&
				def.getInput(0).getOffset() == 0 && def.getInput(1).isConstant()
						? addressOf(program, def.getInput(1), depth + 1)
						: null;
			default -> null;
		};
	}

	/**
	 * The addresses a value may be (see {@link #addressOf}), through the merges of several,
	 * as in {@code f(flag ? &a : &b)}, and the copies and casts between them, as a merge of
	 * constants copied to a variable that another merge takes
	 */
	static Set<Address> addressesOf(Program program, Varnode value) {
		Set<Address> addresses = new LinkedHashSet<>();
		addressesOf(program, value, 0, addresses);
		return addresses;
	}

	private static void addressesOf(Program program, Varnode value, int depth,
			Set<Address> addresses) {
		if (value == null || depth > 6) {
			return;
		}
		PcodeOp def = unwrap(value).getDef();
		if (def != null && def.getOpcode() == PcodeOp.MULTIEQUAL) {
			for (int i = 0; i < def.getNumInputs(); i++) {
				addressesOf(program, def.getInput(i), depth + 1, addresses);
			}
			return;
		}
		Address address = addressOf(program, value, 0);
		if (address != null) {
			addresses.add(address);
		}
	}

	/** A value without the casts and copies the decompiler put on it */
	static Varnode unwrap(Varnode value) {
		for (int depth = 0; value != null && depth < 4; depth++) {
			PcodeOp def = value.getDef();
			if (def == null ||
				def.getOpcode() != PcodeOp.CAST && def.getOpcode() != PcodeOp.COPY) {
				break;
			}
			value = def.getInput(0);
		}
		return value;
	}

	/**
	 * The pointer type that the uses of a loaded untyped value cast it to, as in
	 * {@code (float *)tbl[i].f4} or a call's {@code (S *)} parameter, if they agree
	 */
	static DataType castTo(Varnode value) {
		DataType type = null;
		Iterator<PcodeOp> uses = value.getDescendants();
		while (uses.hasNext()) {
			PcodeOp op = uses.next();
			if (op.getOpcode() != PcodeOp.CAST || op.getOutput().getHigh() == null) {
				continue;
			}
			DataType t = op.getOutput().getHigh().getDataType();
			if (!(t instanceof Pointer) || !E200Types.informative(t) ||
				t.getLength() != value.getSize()) {
				continue;
			}
			if (type != null && !type.isEquivalent(t)) {
				return null;
			}
			type = t;
		}
		return type;
	}

	/**
	 * The pointer types that the code casts a loaded value to after arithmetic on it, as in
	 * {@code *(float *)((int)p->values + i * 4)}: what the value points to when the code
	 * chooses the type at run time
	 */
	static List<DataType> castsAfterArithmetic(Varnode value) {
		List<DataType> casts = new ArrayList<>();
		for (PcodeOp op : castOpsAfterArithmetic(value)) {
			casts.add(op.getOutput().getHigh().getDataType());
		}
		return casts;
	}

	/** The CAST ops of {@link #castsAfterArithmetic} */
	static List<PcodeOp> castOpsAfterArithmetic(Varnode value) {
		List<PcodeOp> casts = new ArrayList<>();
		Set<Varnode> seen = new HashSet<>();
		Deque<Varnode> todo = new ArrayDeque<>();
		todo.add(value);
		while (!todo.isEmpty() && seen.size() < 64) {
			Varnode v = todo.pop();
			if (v == null || !seen.add(v)) {
				continue;
			}
			Iterator<PcodeOp> uses = v.getDescendants();
			while (uses.hasNext()) {
				PcodeOp op = uses.next();
				Varnode out = op.getOutput();
				switch (op.getOpcode()) {
					case PcodeOp.CAST -> {
						DataType t = out.getHigh() == null ? null : out.getHigh().getDataType();
						if (t instanceof Pointer && E200Types.informative(t)) {
							casts.add(op);
						}
						else {
							todo.add(out); // to an integer, for the arithmetic
						}
					}
					case PcodeOp.COPY, PcodeOp.MULTIEQUAL, PcodeOp.INT_ADD, PcodeOp.PTRADD,
							PcodeOp.INT_SUB -> todo.add(out);
					default -> {
						// not the pointer any more
					}
				}
			}
		}
		return casts;
	}

	/**
	 * The comparison with a constant that holds where an op is: the op's block is the branch
	 * that {@code x == 8} leads to (or the other branch of {@code x != 8}), up a chain of
	 * blocks with one predecessor each; the value compared and the constant, or null
	 */
	static Map.Entry<Varnode, Long> guard(PcodeOp op) {
		if (!(op instanceof PcodeOpAST ast)) {
			return null;
		}
		PcodeBlock block = ast.getParent();
		for (int depth = 0; block != null && depth < 6; depth++) {
			for (int i = 0; i < block.getInSize(); i++) {
				PcodeBlock in = block.getIn(i);
				PcodeOp last = in instanceof PcodeBlockBasic basic ? basic.getLastOp() : null;
				if (last == null || last.getOpcode() != PcodeOp.CBRANCH) {
					continue;
				}
				Map.Entry<Varnode, Long> comparison =
					comparison(last.getInput(1), in.getTrueOut() == block);
				if (comparison != null) {
					return comparison;
				}
			}
			block = block.getInSize() == 1 ? block.getIn(0) : null;
		}
		return null;
	}

	/** A comparison of a value with a constant: whether the value equals it or differs */
	record Comparison(Varnode value, long constant, boolean equal) {}

	/** The float operations of p-code */
	private static final Set<Integer> FLOAT_OPS = Set.of(PcodeOp.FLOAT_EQUAL,
		PcodeOp.FLOAT_NOTEQUAL, PcodeOp.FLOAT_LESS, PcodeOp.FLOAT_LESSEQUAL, PcodeOp.FLOAT_NAN,
		PcodeOp.FLOAT_ADD, PcodeOp.FLOAT_DIV, PcodeOp.FLOAT_MULT, PcodeOp.FLOAT_SUB,
		PcodeOp.FLOAT_NEG, PcodeOp.FLOAT_ABS, PcodeOp.FLOAT_SQRT, PcodeOp.FLOAT_FLOAT2FLOAT,
		PcodeOp.FLOAT_TRUNC, PcodeOp.FLOAT_CEIL, PcodeOp.FLOAT_FLOOR, PcodeOp.FLOAT_ROUND);

	/**
	 * The ops that use a value, through copies and casts, as the float operations in the
	 * branches that use a value loaded before them; null if the value goes into a merge, as a
	 * variable that other paths set too, whose uses lie anywhere
	 */
	static List<PcodeOp> consumers(Varnode value) {
		List<PcodeOp> consumers = new ArrayList<>();
		Deque<Varnode> todo = new ArrayDeque<>();
		Set<Varnode> seen = new HashSet<>();
		todo.add(value);
		while (!todo.isEmpty()) {
			Varnode v = todo.pop();
			if (v == null || !seen.add(v)) {
				continue;
			}
			if (seen.size() > 32) {
				return null;
			}
			Iterator<PcodeOp> uses = v.getDescendants();
			while (uses.hasNext()) {
				PcodeOp op = uses.next();
				switch (op.getOpcode()) {
					case PcodeOp.COPY, PcodeOp.CAST -> todo.add(op.getOutput());
					case PcodeOp.MULTIEQUAL, PcodeOp.INDIRECT -> {
						return null;
					}
					default -> consumers.add(op);
				}
			}
		}
		return consumers;
	}

	/**
	 * Whether a value is used, and only as a float: in float operations, or cast to a float
	 * type, as the decompiler shows {@code (float)p[1].f4} where the field type of the next
	 * element says pointer
	 */
	static boolean usedAsFloat(Varnode value) {
		boolean used = false;
		Deque<Varnode> todo = new ArrayDeque<>();
		Set<Varnode> seen = new HashSet<>();
		todo.add(value);
		while (!todo.isEmpty()) {
			Varnode v = todo.pop();
			if (v == null || !seen.add(v)) {
				continue;
			}
			if (seen.size() > 16) {
				return false;
			}
			Iterator<PcodeOp> uses = v.getDescendants();
			while (uses.hasNext()) {
				PcodeOp op = uses.next();
				if (op.getOpcode() == PcodeOp.COPY) {
					todo.add(op.getOutput());
					continue;
				}
				if (op.getOpcode() == PcodeOp.CAST) {
					HighVariable high = op.getOutput().getHigh();
					if (high == null || !(high.getDataType() instanceof AbstractFloatDataType)) {
						return false;
					}
				}
				else if (!FLOAT_OPS.contains(op.getOpcode())) {
					return false;
				}
				used = true;
			}
		}
		return used;
	}

	/**
	 * The comparisons with constants that hold where an op is: the branches taken on the way
	 * to its block, up the chain of blocks with one predecessor each (see {@link #guard}),
	 * as {@code p->type != 0} and {@code p->type == 8} on the way to a load in the branch
	 * of a switch on the type
	 */
	static List<Comparison> guards(PcodeOp op) {
		List<Comparison> guards = new ArrayList<>();
		if (!(op instanceof PcodeOpAST ast)) {
			return guards;
		}
		PcodeBlock block = ast.getParent();
		for (int depth = 0; block != null && block.getInSize() == 1 && depth < 8; depth++) {
			PcodeBlock in = block.getIn(0);
			PcodeOp last = in instanceof PcodeBlockBasic basic ? basic.getLastOp() : null;
			if (last != null && last.getOpcode() == PcodeOp.CBRANCH) {
				Comparison c = comparisonOf(last.getInput(1), in.getTrueOut() == block, 0);
				if (c != null) {
					guards.add(c);
				}
			}
			block = in;
		}
		return guards;
	}

	/**
	 * The comparison a condition is, if it {@code holds}, or its opposite if it does not;
	 * null for other conditions
	 */
	private static Comparison comparisonOf(Varnode condition, boolean holds, int depth) {
		PcodeOp def = condition == null || depth > 4 ? null : condition.getDef();
		if (def == null) {
			return null;
		}
		switch (def.getOpcode()) {
			case PcodeOp.BOOL_NEGATE -> {
				return comparisonOf(def.getInput(0), !holds, depth + 1);
			}
			case PcodeOp.INT_EQUAL, PcodeOp.INT_NOTEQUAL -> {
				boolean equal = def.getOpcode() == PcodeOp.INT_EQUAL == holds;
				Varnode a = def.getInput(0);
				Varnode b = def.getInput(1);
				if (b.isConstant() && !a.isConstant()) {
					return new Comparison(a, b.getOffset(), equal);
				}
				if (a.isConstant() && !b.isConstant()) {
					return new Comparison(b, a.getOffset(), equal);
				}
				return null;
			}
			default -> {
				return null;
			}
		}
	}

	/**
	 * The value and constant that a condition says are equal, if it {@code holds}, or that
	 * it says differ if it does not; null for other conditions
	 */
	private static Map.Entry<Varnode, Long> comparison(Varnode condition, boolean holds) {
		PcodeOp def = condition == null ? null : condition.getDef();
		if (def == null) {
			return null;
		}
		switch (def.getOpcode()) {
			case PcodeOp.BOOL_NEGATE -> {
				return comparison(def.getInput(0), !holds);
			}
			case PcodeOp.INT_EQUAL, PcodeOp.INT_NOTEQUAL -> {
				if (def.getOpcode() == PcodeOp.INT_EQUAL != holds) {
					return null; // the branch where they differ says nothing
				}
				Varnode a = def.getInput(0);
				Varnode b = def.getInput(1);
				if (b.isConstant() && !a.isConstant()) {
					return Map.entry(a, b.getOffset());
				}
				if (a.isConstant() && !b.isConstant()) {
					return Map.entry(b, a.getOffset());
				}
				return null;
			}
			default -> {
				return null;
			}
		}
	}

	/**
	 * The loads that a value derives from through arithmetic, copies, casts, extensions and
	 * merges, as the index of an array access derives from the count field of a descriptor
	 * ({@code p->x[p->n - 1]}), with whether arithmetic lies between (a value that is the
	 * index as it is, {@code p->x[p->i]}, is an index, not a count); at most {@code limit}
	 * ops are followed
	 */
	static Map<PcodeOp, Boolean> loadsBehind(Varnode value, int limit) {
		Map<PcodeOp, Boolean> loads = new LinkedHashMap<>();
		Map<Varnode, Boolean> seen = new HashMap<>();
		Deque<Map.Entry<Varnode, Boolean>> todo = new ArrayDeque<>();
		todo.add(Map.entry(value, false));
		while (!todo.isEmpty() && seen.size() < limit) {
			Map.Entry<Varnode, Boolean> e = todo.pop();
			Varnode v = e.getKey();
			boolean arithmetic = e.getValue();
			if (v == null || v.isConstant() ||
				seen.containsKey(v) && (seen.get(v) || !arithmetic)) {
				continue;
			}
			seen.put(v, arithmetic);
			PcodeOp def = v.getDef();
			if (def == null) {
				continue;
			}
			switch (def.getOpcode()) {
				case PcodeOp.LOAD -> loads.merge(def, arithmetic, Boolean::logicalOr);
				case PcodeOp.COPY, PcodeOp.CAST, PcodeOp.INT_SEXT, PcodeOp.INT_ZEXT,
						PcodeOp.MULTIEQUAL, PcodeOp.SUBPIECE -> {
					for (int i = 0; i < def.getNumInputs(); i++) {
						todo.add(Map.entry(def.getInput(i), arithmetic));
					}
				}
				case PcodeOp.INT_NEGATE, PcodeOp.INT_2COMP, PcodeOp.INT_ADD, PcodeOp.INT_SUB,
						PcodeOp.INT_MULT, PcodeOp.INT_LEFT, PcodeOp.INT_RIGHT, PcodeOp.INT_SRIGHT,
						PcodeOp.INT_AND, PcodeOp.INT_OR, PcodeOp.INT_XOR, PcodeOp.PTRADD,
						PcodeOp.PTRSUB -> {
					for (int i = 0; i < def.getNumInputs(); i++) {
						todo.add(Map.entry(def.getInput(i), true));
					}
				}
				default -> {
					// a call's result, a comparison: not an index of the structure's fields
				}
			}
		}
		return loads;
	}

	/**
	 * What a loaded value points to, from the loads and stores through it (through copies
	 * and casts): the type the accesses agree on, where a value read has none the type code
	 * casts it to or copies it into ({@code (char)*p}, {@code BYTE_x = *p}); null if the value
	 * is not dereferenced, the sizes differ or no access has a type (a pointer to an undefined
	 * value would keep the data at the targets from the type a later step gives it)
	 */
	static DataType pointee(Varnode value) {
		int size = 0;
		List<DataType> types = new ArrayList<>();
		Deque<Varnode> todo = new ArrayDeque<>();
		Set<Varnode> seen = new HashSet<>();
		todo.add(value);
		while (!todo.isEmpty() && seen.size() < 6) {
			Varnode v = todo.pop();
			if (v == null || !seen.add(v)) {
				continue;
			}
			Iterator<PcodeOp> uses = v.getDescendants();
			while (uses.hasNext()) {
				PcodeOp op = uses.next();
				switch (op.getOpcode()) {
					case PcodeOp.COPY, PcodeOp.CAST -> todo.add(op.getOutput());
					case PcodeOp.LOAD, PcodeOp.STORE -> {
						if (op.getInput(1) != v) {
							continue;
						}
						Varnode accessed = op.getOpcode() == PcodeOp.LOAD ? op.getOutput()
								: op.getInput(2);
						if (accessed == null || size != 0 && accessed.getSize() != size) {
							return null;
						}
						size = accessed.getSize();
						DataType t = accessed.getHigh() == null ? null
								: accessed.getHigh().getDataType();
						if (E200Types.informative(t) && t.getLength() == size &&
							!(t instanceof Pointer)) {
							types.add(t);
						}
						else if (op.getOpcode() == PcodeOp.LOAD) {
							// an untyped value read: what code casts it to or copies it into,
							// as (char)*p and BYTE_x = *p
							Iterator<PcodeOp> valueUses = accessed.getDescendants();
							while (valueUses.hasNext()) {
								PcodeOp u = valueUses.next();
								HighVariable high = u.getOutput() == null ? null
										: u.getOutput().getHigh();
								DataType ut = high == null ? null : high.getDataType();
								if ((u.getOpcode() == PcodeOp.CAST ||
									u.getOpcode() == PcodeOp.COPY) &&
									E200Types.informative(ut) && ut.getLength() == size &&
									!(ut instanceof Pointer)) {
									types.add(ut);
								}
							}
						}
					}
					default -> {
						// not a use as the address
					}
				}
			}
		}
		if (size == 0 || types.isEmpty()) {
			return null;
		}
		DataType type = E200Types.chooseType(types, false, true);
		return type != null && type.getLength() == size ? type : null;
	}

	/** The LOAD a value comes from, through copies, casts and extensions; null if none */
	static PcodeOp loadOf(Varnode value) {
		for (int depth = 0; value != null && depth < 6; depth++) {
			PcodeOp def = value.getDef();
			if (def == null) {
				return null;
			}
			switch (def.getOpcode()) {
				case PcodeOp.LOAD -> {
					return def;
				}
				case PcodeOp.COPY, PcodeOp.CAST, PcodeOp.INT_ZEXT, PcodeOp.INT_SEXT -> value =
					def.getInput(0);
				default -> {
					return null;
				}
			}
		}
		return null;
	}

	/** The value of a constant varnode, sign extended from its size */
	static long signed(Varnode constant) {
		long value = constant.getOffset();
		int bits = constant.getSize() * 8;
		return bits >= 64 ? value : value << (64 - bits) >> (64 - bits);
	}

	/** The multiplier of an index, as in {@code i * 0x14} or {@code i << 2}, else 1 */
	static long stride(Varnode index) {
		PcodeOp def = index.getDef();
		if (def == null) {
			return 1;
		}
		return switch (def.getOpcode()) {
			case PcodeOp.INT_MULT -> def.getInput(1).isConstant() ? def.getInput(1).getOffset()
					: def.getInput(0).isConstant() ? def.getInput(0).getOffset() : 1;
			case PcodeOp.INT_LEFT -> def.getInput(1).isConstant() &&
				def.getInput(1).getOffset() < 16 ? 1L << def.getInput(1).getOffset() : 1;
			case PcodeOp.CAST, PcodeOp.COPY, PcodeOp.INT_ZEXT, PcodeOp.INT_SEXT ->
				stride(def.getInput(0));
			default -> 1;
		};
	}
}
