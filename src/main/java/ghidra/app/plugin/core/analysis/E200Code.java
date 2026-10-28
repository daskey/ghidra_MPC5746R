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
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.Pointer;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.Varnode;

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
	 * as in {@code f(flag ? &a : &b)}
	 */
	static Set<Address> addressesOf(Program program, Varnode value) {
		Set<Address> addresses = new LinkedHashSet<>();
		addressesOf(program, value, 0, addresses);
		return addresses;
	}

	private static void addressesOf(Program program, Varnode value, int depth,
			Set<Address> addresses) {
		if (value == null || depth > 4) {
			return;
		}
		PcodeOp def = value.getDef();
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
							casts.add(t);
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
