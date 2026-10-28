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

import ghidra.program.model.data.*;
import ghidra.program.model.data.Enum;

/**
 * The data types the analysis chooses and makes (shared by the steps of
 * {@link E200DataTypes}): the kinds of types that say something, the integer types of a size
 * and signedness, and the type that the uses of a value agree on.
 */
final class E200Types {

	/** Category of the structures and function definitions the analyzer creates */
	static final CategoryPath CATEGORY = new CategoryPath("/E200");

	/** The kinds of types that single values have */
	enum Kind {
		FLOAT, INTEGER, POINTER, OTHER
	}

	private E200Types() {
	}

	// ---- Kinds of types -----------------------------------------------------------------------

	/** Whether a type is a structure the analyzer created */
	static boolean ownStructure(DataType type) {
		return type instanceof Structure s && s.getCategoryPath().equals(CATEGORY);
	}

	/** Whether a type is a pointer to a structure the analyzer created */
	static boolean ownStructurePointer(DataType type) {
		return type instanceof Pointer p && ownStructure(p.getDataType());
	}

	/** Whether the type says more than its size */
	static boolean informative(DataType type) {
		if (type == null || Undefined.isUndefined(type) || type instanceof VoidDataType) {
			return false;
		}
		if (type instanceof Pointer pointer) {
			DataType target = pointer.getDataType();
			return target != null && informative(target);
		}
		return true;
	}

	/** Whether a type is a single value: an integer, float, pointer, enum or undefined */
	static boolean primitive(DataType type) {
		DataType base = type instanceof TypeDef t ? t.getBaseDataType() : type;
		return base instanceof AbstractIntegerDataType || base instanceof AbstractFloatDataType ||
			base instanceof Pointer || base instanceof Undefined ||
			base instanceof DefaultDataType || base instanceof Enum;
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

	static Kind kind(DataType type) {
		DataType base = type instanceof TypeDef t ? t.getBaseDataType() : type;
		if (base instanceof AbstractFloatDataType) {
			return Kind.FLOAT;
		}
		if (base instanceof AbstractIntegerDataType || base instanceof Enum) {
			return Kind.INTEGER;
		}
		if (base instanceof Pointer) {
			return Kind.POINTER;
		}
		return Kind.OTHER;
	}

	/**
	 * Whether {@code type} can replace {@code current}: an undefined type of its size, or a
	 * pointer to undefined data, by a pointer to data of that size (any size for a pointer to
	 * {@code undefined})
	 */
	static boolean fits(DataType current, DataType type) {
		if (current == null || type == null || type.getLength() != current.getLength()) {
			return false;
		}
		if (Undefined.isUndefined(current)) {
			return !(current instanceof DefaultDataType);
		}
		if (current instanceof Pointer p && type instanceof Pointer q) {
			DataType from = p.getDataType();
			DataType to = q.getDataType();
			if (from == null || to == null) {
				return false;
			}
			if (from instanceof DefaultDataType) {
				return true;
			}
			if (Undefined.isUndefined(from)) {
				return to.getLength() == from.getLength();
			}
			return fits(from, to);
		}
		return false;
	}

	// ---- Integers -----------------------------------------------------------------------------

	/** The unsigned integer of 1, 2, 4 or 8 bytes, or null */
	static DataType unsigned(int length) {
		return switch (length) {
			case 1 -> ByteDataType.dataType;
			case 2 -> UnsignedShortDataType.dataType;
			case 4 -> UnsignedIntegerDataType.dataType;
			case 8 -> UnsignedLongLongDataType.dataType;
			default -> null;
		};
	}

	/** The signed integer of 1, 2, 4 or 8 bytes, or null */
	static DataType signed(int length) {
		return switch (length) {
			case 1 -> SignedByteDataType.dataType;
			case 2 -> ShortDataType.dataType;
			case 4 -> IntegerDataType.dataType;
			case 8 -> LongLongDataType.dataType;
			default -> null;
		};
	}

	/**
	 * An integer type of the size of {@code type}, signed if {@code evidence} is positive,
	 * else unsigned; other types as they are
	 */
	static DataType withSign(DataType type, int evidence) {
		if (!integer(type)) {
			return type;
		}
		return evidence > 0 ? signed(type.getLength()) : unsigned(type.getLength());
	}

	private static boolean isUnsigned(DataType type) {
		DataType base = type instanceof TypeDef t ? t.getBaseDataType() : type;
		return base instanceof UnsignedIntegerDataType || base instanceof UnsignedShortDataType ||
			base instanceof ByteDataType || base instanceof UnsignedLongLongDataType ||
			(base instanceof Pointer p && isUnsigned(p.getDataType()));
	}

	// ---- Agreement ----------------------------------------------------------------------------

	/**
	 * The type that the types of the uses of a value agree on, or null when they disagree.
	 *
	 * @param types the types of the uses
	 * @param signedChar whether plain {@code char} is signed in the program
	 * @param floatWins whether a {@code float} wins over integers of its size, as for the uses
	 * of one global, where values that are only copied look like integers
	 */
	static DataType chooseType(List<DataType> types, boolean signedChar, boolean floatWins) {
		return chooseType(types, signedChar, floatWins, false);
	}

	/**
	 * {@link #chooseType(List, boolean, boolean)}, with {@code unsignedTieBreak} choosing the
	 * unsigned integer where as many uses are signed as unsigned
	 */
	static DataType chooseType(List<DataType> types, boolean signedChar, boolean floatWins,
			boolean unsignedTieBreak) {
		Map<String, DataType> distinct = new LinkedHashMap<>();
		Map<String, Integer> counts = new HashMap<>();
		for (DataType t : types) {
			DataType type = normalizeChars(t, signedChar);
			if (kind(type) == Kind.OTHER) {
				return null;
			}
			String key = type.getPathName() + "/" + type.getLength();
			distinct.putIfAbsent(key, type);
			counts.merge(key, 1, Integer::sum);
		}
		if (distinct.isEmpty()) {
			return null;
		}
		if (distinct.size() == 1) {
			return distinct.values().iterator().next();
		}
		int length = -1;
		List<DataType> floats = new ArrayList<>();
		boolean allPointers = true;
		for (DataType type : distinct.values()) {
			if (length >= 0 && type.getLength() != length) {
				return null;
			}
			length = type.getLength();
			if (kind(type) != Kind.POINTER) {
				allPointers = false;
			}
			if (kind(type) == Kind.FLOAT) {
				floats.add(type);
			}
		}
		if (allPointers) {
			List<DataType> targets = distinct.values()
					.stream()
					.map(p -> ((Pointer) p).getDataType())
					.filter(Objects::nonNull)
					.toList();
			DataType target = chooseType(targets, signedChar, floatWins, unsignedTieBreak);
			return target == null ? null : new PointerDataType(target, length);
		}
		if (floats.size() == 1 && floatWins) {
			return floats.get(0);
		}
		if (!floats.isEmpty()) {
			return null;
		}
		// integers that differ in signedness: the clear majority
		DataType chosen = null;
		int best = 0;
		boolean tie = false;
		for (Map.Entry<String, Integer> e : counts.entrySet()) {
			if (e.getValue() > best) {
				best = e.getValue();
				chosen = distinct.get(e.getKey());
				tie = false;
			}
			else if (e.getValue() == best) {
				tie = true;
			}
		}
		if (!tie) {
			return chosen;
		}
		if (!unsignedTieBreak) {
			return null;
		}
		for (Map.Entry<String, Integer> e : counts.entrySet()) {
			if (e.getValue() == best && isUnsigned(distinct.get(e.getKey()))) {
				return distinct.get(e.getKey());
			}
		}
		return unsigned(length);
	}

	/** The type with {@code byte} or {@code sbyte} for a character type, in pointers too */
	private static DataType normalizeChars(DataType type, boolean signedChar) {
		if (type == null) {
			return null;
		}
		if (type instanceof CharDataType && type.getLength() == 1) {
			boolean signed = type instanceof SignedCharDataType ||
				(!(type instanceof UnsignedCharDataType) && signedChar);
			return signed ? SignedByteDataType.dataType : ByteDataType.dataType;
		}
		if (type instanceof Pointer p && p.getDataType() != null) {
			DataType target = normalizeChars(p.getDataType(), signedChar);
			if (target != p.getDataType()) {
				return new PointerDataType(target, p.getLength());
			}
		}
		return type;
	}

	/** The most frequent of the sizes, the larger on a tie; 0 if there are none */
	static int mostFrequent(Collection<Integer> sizes) {
		Map<Integer, Integer> counts = new HashMap<>();
		sizes.forEach(size -> counts.merge(size, 1, Integer::sum));
		int size = 0;
		int count = 0;
		for (Map.Entry<Integer, Integer> e : counts.entrySet()) {
			if (e.getValue() > count || e.getValue() == count && e.getKey() > size) {
				size = e.getKey();
				count = e.getValue();
			}
		}
		return size;
	}
}
