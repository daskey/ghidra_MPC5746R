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

import java.util.Iterator;

import ghidra.program.model.data.*;
import ghidra.program.model.pcode.*;

/**
 * The signedness and width of integer values from what code does with them (part of
 * {@link E200DataTypes}).
 * <p>
 * The decompiler infers integer types before it removes dead code. The compare instructions
 * {@code se_cmp}, {@code se_cmpi} and {@code e_cmpi}, which compilers also use to test for
 * equality, set the less and greater bits of the condition register with signed comparisons,
 * so a value that code only compares for equality comes out signed even where nothing but the
 * equal bit is used. AUTOSAR code, whose {@code uint8} and {@code uint32} values are mostly
 * compared for equality, comes out mostly signed.
 * <p>
 * The signedness of an integer is taken instead from the operations on it that remain in the
 * decompiled code: sign extension, signed comparisons, arithmetic shifts right and signed
 * division make it signed, their unsigned counterparts unsigned. A comparison of a value
 * extended to an {@code int} says nothing about the value itself (C promotes a
 * {@code uint8} to an {@code int} before comparing it). A value without either kind of use,
 * only copied, compared for equality or computed with, is unsigned.
 * <p>
 * A parameter of one or two bytes arrives in a register that the callee masks or truncates
 * before every use ({@code e_rlwinm r0,r3,0,24,31}), and Decompiler Parameter ID gives it the
 * register's four bytes: the decompiler shows {@code param_1 & 0xff} at each use, and casts
 * at each call. A parameter all of whose uses are such is one or two bytes wide, and so is a
 * return value that every caller uses so.
 */
final class E200Integers {

	private E200Integers() {
	}

	/**
	 * How the uses of a value show its signedness: the number of uses that treat it as
	 * signed less those that treat it as unsigned
	 */
	static int evidence(HighVariable high) {
		if (high == null) {
			return 0;
		}
		int evidence = 0;
		for (Varnode v : high.getInstances()) {
			evidence += evidence(v);
		}
		return evidence;
	}

	/** The evidence of a single varnode: its definition and its uses */
	private static int evidence(Varnode v) {
		int evidence = 0;
		PcodeOp def = v.getDef();
		if (def != null) {
			if (def.getOpcode() == PcodeOp.INT_SEXT) {
				evidence++;
			}
			else if (def.getOpcode() == PcodeOp.INT_ZEXT) {
				evidence--;
			}
		}
		Iterator<PcodeOp> uses = v.getDescendants();
		while (uses.hasNext()) {
			PcodeOp op = uses.next();
			boolean first = op.getNumInputs() > 0 && op.getInput(0) == v;
			switch (op.getOpcode()) {
				case PcodeOp.INT_SEXT -> evidence++;
				case PcodeOp.INT_ZEXT -> evidence--;
				case PcodeOp.INT_SLESS, PcodeOp.INT_SLESSEQUAL, PcodeOp.INT_SDIV,
						PcodeOp.INT_SREM -> evidence++;
				case PcodeOp.INT_LESS, PcodeOp.INT_LESSEQUAL, PcodeOp.INT_DIV,
						PcodeOp.INT_REM -> evidence--;
				case PcodeOp.INT_SRIGHT -> evidence += first ? 1 : 0;
				case PcodeOp.INT_RIGHT -> evidence -= first ? 1 : 0;
				default -> {
					// copied, compared for equality, or computed with
				}
			}
		}
		return evidence;
	}

	/**
	 * The width in bytes that the uses of a value of four bytes show: 1 or 2 if every use
	 * masks it with 0xff or 0xffff or truncates it to that width, 0 if it has no use, else 4;
	 * and through {@code evidence} the signedness evidence of the narrowed values
	 */
	static int width(HighVariable high, int[] evidence) {
		if (high == null || high.getSize() != 4) {
			return 4;
		}
		int width = 0;
		for (Varnode v : high.getInstances()) {
			Iterator<PcodeOp> uses = v.getDescendants();
			while (uses.hasNext()) {
				PcodeOp op = uses.next();
				int w = 4;
				if (op.getOpcode() == PcodeOp.INT_AND && op.getInput(1).isConstant()) {
					long mask = op.getInput(1).getOffset();
					w = mask == 0xff ? 1 : mask == 0xffff ? 2 : 4;
				}
				else if (op.getOpcode() == PcodeOp.SUBPIECE && op.getInput(0) == v &&
					op.getInput(1).getOffset() == 0 && op.getOutput().getSize() <= 2) {
					w = op.getOutput().getSize();
					evidence[0] += evidence(op.getOutput().getHigh());
				}
				else if ((op.getOpcode() == PcodeOp.INDIRECT ||
					op.getOpcode() == PcodeOp.MULTIEQUAL) && op.getOutput().getHigh() == high) {
					continue; // within the variable
				}
				width = Math.max(width, w);
			}
		}
		return width;
	}

	/**
	 * The width in bytes of the value a 4-byte value is extended from, 1 or 2 if it is a byte
	 * or halfword zero or sign extended, or masked to one, on every path (through copies and
	 * merges of such values, and small constants), with the signedness the extensions show
	 * (positive for sign extensions); 0 if only small constants are known; null if it is not
	 * extended from one, or the value is not known
	 */
	static int[] extended(Varnode v, int depth) {
		if (v == null || depth > 6) {
			return null;
		}
		if (v.isConstant()) {
			// a small constant fits any width and says nothing about it
			long value = v.getOffset();
			return value >= 0 && value <= 0xffff ? new int[] { 0, 0 } : null;
		}
		if (v.getSize() <= 2) {
			return new int[] { v.getSize(), 0 };
		}
		PcodeOp def = v.getDef();
		if (def == null) {
			return null;
		}
		switch (def.getOpcode()) {
			case PcodeOp.INT_ZEXT, PcodeOp.INT_SEXT -> {
				int size = def.getInput(0).getSize();
				return size > 2 ? null
						: new int[] { size, def.getOpcode() == PcodeOp.INT_SEXT ? 1 : -1 };
			}
			case PcodeOp.INT_AND -> {
				Varnode mask = def.getInput(1).isConstant() ? def.getInput(1)
						: def.getInput(0).isConstant() ? def.getInput(0) : null;
				if (mask == null) {
					return null;
				}
				return mask.getOffset() == 0xff ? new int[] { 1, -1 }
						: mask.getOffset() == 0xffff ? new int[] { 2, -1 } : null;
			}
			case PcodeOp.COPY, PcodeOp.CAST -> {
				return extended(def.getInput(0), depth + 1);
			}
			case PcodeOp.MULTIEQUAL -> {
				int[] result = null;
				for (int i = 0; i < def.getNumInputs(); i++) {
					int[] in = extended(def.getInput(i), depth + 1);
					if (in == null) {
						return null;
					}
					result = result == null ? in
							: new int[] { Math.max(result[0], in[0]), result[1] + in[1] };
				}
				return result;
			}
			default -> {
				return null;
			}
		}
	}

	/** The type the decompiler gives a value, an integer with the signedness its uses show */
	static DataType of(HighVariable high) {
		if (high == null) {
			return null;
		}
		return withSign(high.getDataType(), evidence(high));
	}

	/** {@link #of(HighVariable)} for the variable of a varnode, or null */
	static DataType of(Varnode v) {
		return v == null ? null : of(v.getHigh());
	}

	/**
	 * An integer type of the size of {@code type}, signed if {@code evidence} is positive,
	 * else unsigned; other types as they are
	 */
	static DataType withSign(DataType type, int evidence) {
		if (!integer(type)) {
			return type;
		}
		return evidence > 0 ? signed(type.getLength()) : E200DataTypes.unsigned(type.getLength());
	}

	/** Whether a type is an integer of 1, 2, 4 or 8 bytes, a character included, not a boolean */
	static boolean integer(DataType type) {
		DataType base = type instanceof TypeDef t ? t.getBaseDataType() : type;
		if (!(base instanceof AbstractIntegerDataType) || base instanceof BooleanDataType) {
			return false;
		}
		int length = base.getLength();
		return length == 1 || length == 2 || length == 4 || length == 8;
	}

	private static DataType signed(int length) {
		return switch (length) {
			case 1 -> SignedByteDataType.dataType;
			case 2 -> ShortDataType.dataType;
			case 8 -> LongLongDataType.dataType;
			default -> IntegerDataType.dataType;
		};
	}
}
