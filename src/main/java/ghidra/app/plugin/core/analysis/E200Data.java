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

import java.util.ArrayList;
import java.util.List;

import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.exception.InvalidInputException;

/**
 * Operations on the data of the listing (shared by the steps of {@link E200Analyzer}):
 * replacing data by data of another type, labels, the structures at data that code passes by
 * address, and the data that pointers point to.
 */
final class E200Data {

	/** Pointers in one piece of data whose targets are typed */
	private static final int MAX_POINTERS = 4096;

	private E200Data() {
	}

	/**
	 * Replaces the data at an address by data of a type of the same length; returns whether
	 * it did. If the new data cannot be created, the old data is restored.
	 */
	static boolean replace(Listing listing, Address address, DataType type) {
		Data data = listing.getDefinedDataAt(address);
		if (data == null || data.getLength() != type.getLength()) {
			return false;
		}
		DataType old = data.getDataType();
		try {
			listing.clearCodeUnits(address, data.getMaxAddress(), false);
			listing.createData(address, type);
			return true;
		}
		catch (CodeUnitInsertionException e) {
			try {
				listing.createData(address, old);
			}
			catch (CodeUnitInsertionException e2) {
				// the old data could not be restored either; the bytes stay undefined
			}
			return false;
		}
	}

	/** Labels an address, unless it has a label already that is not the default one */
	static void label(Program program, Address address, String name, SourceType source) {
		SymbolTable symbols = program.getSymbolTable();
		Symbol primary = symbols.getPrimarySymbol(address);
		if (primary != null && primary.getSource() != SourceType.DEFAULT) {
			return;
		}
		try {
			symbols.createLabel(address, name, source);
		}
		catch (InvalidInputException e) {
			// not a valid name
		}
	}

	/**
	 * Gives the data at an address that code passes as a pointer to a structure that
	 * structure, where there are only single values there, at fields of their size, or
	 * structures of the analyzer's that lie inside it (the larger structure wins, whichever
	 * is applied first); returns whether it did. The data its pointer fields point to gets the
	 * pointed-to type (see {@link #targets}).
	 */
	static boolean structureAt(Program program, Address address, Structure s) {
		Listing listing = program.getListing();
		MemoryBlock block = program.getMemory().getBlock(address);
		if (block == null || block.isVolatile() ||
			program.getFunctionManager().getFunctionContaining(address) != null) {
			return false;
		}
		Address end;
		try {
			end = address.addNoWrap(s.getLength() - 1);
		}
		catch (AddressOverflowException e) {
			return false;
		}
		Data at = listing.getDataContaining(address);
		if (!block.contains(end) || at != null && (!at.getAddress().equals(address) ||
			!E200Types.primitive(at.getDataType()) && !smallerStructure(at, s))) {
			return false;
		}
		AddressSet range = new AddressSet(address, end);
		if (listing.getInstructions(range, true).hasNext()) {
			return false;
		}
		for (Data d : listing.getDefinedData(range, true)) {
			DataType t = d.getDataType();
			if (d.getMaxAddress().compareTo(end) > 0) {
				return false;
			}
			if (smallerStructure(d, s)) {
				continue; // a structure of the analyzer's inside this one: the larger wins
			}
			if (!E200Types.primitive(t)) {
				return false;
			}
			int offset = (int) d.getAddress().subtract(address);
			DataTypeComponent c = s.getComponentAt(offset);
			if (!Undefined.isUndefined(t) && !integerOverFields(s, offset, d.getLength(), t) &&
				(c == null || c.getDataType() instanceof DefaultDataType ||
					c.getLength() != d.getLength() &&
						!(c.getLength() > d.getLength() && E200Types.integer(c.getDataType()) &&
							E200Types.integer(t)))) {
				return false; // a value that is not a field, nor bytes of integer fields
			}
		}
		try {
			listing.clearCodeUnits(address, end, false);
			listing.createData(address, s);
		}
		catch (CodeUnitInsertionException e) {
			return false;
		}
		targets(program, listing.getDataAt(address), 0);
		return true;
	}

	/** Whether data is a structure of the analyzer's shorter than {@code s} */
	private static boolean smallerStructure(Data d, Structure s) {
		return E200Types.ownStructure(d.getDataType()) && d.getLength() < s.getLength();
	}

	/**
	 * Whether an integer of {@code length} bytes at {@code offset} in a structure covers whole
	 * fields that are integers or undefined, as a halfword that code writes over a byte and
	 * its complement does
	 */
	private static boolean integerOverFields(Structure s, int offset, int length, DataType t) {
		if (!E200Types.integer(t) || offset + length > s.getLength()) {
			return false;
		}
		DataTypeComponent first = s.getComponentAt(offset);
		if (first == null || first.getOffset() != offset) {
			return false;
		}
		for (DataTypeComponent c : s.getComponents()) {
			if (c.getOffset() >= offset && c.getOffset() < offset + length) {
				DataType ct = c.getDataType();
				if (c.getOffset() + c.getLength() > offset + length ||
					!(Undefined.isUndefined(ct) || E200Types.integer(ct))) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Creates data of the pointed-to type where the pointers in new data, its fields and
	 * elements included, point to nothing defined yet, and so on for pointers in that data. In
	 * a flash image all of flash is executable, and the reference analysis would take an
	 * undefined target for code and disassemble it, or for a pointer if its value is an
	 * address, as a float 2.0 (0x40000000, the start of SRAM) is.
	 */
	static void targets(Program program, Data data, int depth) {
		if (data == null || depth > 3) {
			return;
		}
		Listing listing = program.getListing();
		List<Data> fields = new ArrayList<>();
		pointersIn(data, fields, 0);
		for (Data field : fields) {
			if (!(field.getDataType() instanceof Pointer pointer) ||
				!(field.getValue() instanceof Address target)) {
				continue;
			}
			DataType type = pointer.getDataType();
			if (type instanceof VoidDataType) {
				type = ByteDataType.dataType; // what is there is not known, but not code
			}
			MemoryBlock block = program.getMemory().getBlock(target);
			if (type == null || type.getLength() <= 0 || block == null ||
				!block.isInitialized()) {
				continue;
			}
			try {
				Address end = target.addNoWrap(type.getLength() - 1);
				if (!block.contains(end)) {
					continue;
				}
				if (!listing.isUndefined(target, end) && untypedAt(listing, target, end, type)) {
					listing.clearCodeUnits(target, end, false);
				}
				if (listing.isUndefined(target, end)) {
					targets(program, listing.createData(target, type), depth + 1);
				}
			}
			catch (AddressOverflowException | CodeUnitInsertionException e) {
				// no room for the target
			}
		}
	}

	/**
	 * Whether there is only untyped data where a pointer to {@code type} points: undefined
	 * values, or a pointer to nothing in particular of the type's size, which the reference
	 * analysis makes of a value that is an address, as the float 2.0 (0x40000000) is
	 */
	private static boolean untypedAt(Listing listing, Address target, Address end,
			DataType type) {
		if (!E200Types.informative(type) ||
			listing.getInstructions(new AddressSet(target, end), true).hasNext()) {
			return false;
		}
		Data first = listing.getDataContaining(target);
		if (first != null && !first.getAddress().equals(target)) {
			return false;
		}
		for (Data d : listing.getDefinedData(new AddressSet(target, end), true)) {
			DataType t = d.getDataType();
			boolean guessed = t instanceof Pointer p && !E200Types.informative(p) &&
				d.getLength() == type.getLength();
			if (d.getMaxAddress().compareTo(end) > 0 || !Undefined.isUndefined(t) && !guessed) {
				return false;
			}
		}
		return true;
	}

	/** Pointers in data: the data itself, or its components and theirs, as in a table */
	private static void pointersIn(Data data, List<Data> pointers, int level) {
		if (data == null || pointers.size() >= MAX_POINTERS) {
			return;
		}
		if (data.getDataType() instanceof Pointer) {
			pointers.add(data);
			return;
		}
		for (int i = 0; level < 3 && i < data.getNumComponents(); i++) {
			pointersIn(data.getComponent(i), pointers, level + 1);
		}
	}
}
