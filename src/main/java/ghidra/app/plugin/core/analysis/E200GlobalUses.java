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
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.pcode.*;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * The uses of global data in decompiled functions, and the data and types they give (part of
 * {@link E200DataTypes}).
 * <p>
 * The reference analysis creates undefined data wherever code loads or stores a global,
 * knowing only the access size. The decompiler usually knows more: a value used by
 * {@code efs*} instructions is a {@code float}, one that is sign extended is signed, one that
 * is dereferenced is a pointer. A type is committed only when all uses agree, except that a
 * {@code float} use wins over integer uses of the same size (values that are only copied
 * look like integers) and integer uses that differ only in signedness go to a clear
 * majority. Single bytes get {@code byte} or {@code sbyte} rather than a character type.
 * <p>
 * Arrays that code indexes, loading or storing at their address plus an index, have no
 * reference to their start, and tables in flash that code passes by address have no data.
 * {@link E200Tables} creates arrays, and arrays of structures, of the indexed ones. The
 * others get data of the element size or of the size of the pointer's target, typed from
 * the uses, so that the decompiler shows {@code (&BYTE_4000e46e)[i]} instead of
 * {@code *(undefined1 *)(i + 0x4000e46e)} and {@code &SHORT_09294ba0} instead of
 * {@code (short *)&DAT_09294ba0}; undefined data of another size than the pointer's target,
 * as the reference analysis makes of an address an instruction forms, is replaced where
 * nothing accesses the data as it is. Data that code passes as a pointer to a structure of
 * the analyzer's gets the structure (see {@link E200Data#structureAt}).
 */
final class E200GlobalUses {

	/** How code uses a global */
	enum Access {
		/** the value of the global symbol */
		VALUE,
		/** a load or store at its address plus an index, of an array */
		INDEXED,
		/** its address, as a pointer to the type */
		ADDRESS
	}

	/**
	 * A use of a global seen by the decompiler: its address, the inferred type and the size
	 * of the access.
	 */
	record Use(Address address, DataType type, int size, Access access) {}

	private E200GlobalUses() {
	}

	// ---- Collection ---------------------------------------------------------------------------

	/** The uses of globals in a decompiled function */
	static List<Use> collect(HighFunction high) {
		List<Use> uses = new ArrayList<>();
		Program program = high.getFunction().getProgram();
		FunctionManager functions = program.getFunctionManager();
		Listing listing = program.getListing();
		Iterator<HighSymbol> it = high.getGlobalSymbolMap().getSymbols();
		while (it.hasNext()) {
			HighSymbol symbol = it.next();
			HighVariable variable = symbol.getHighVariable();
			if (variable == null || symbol.getStorage() == null ||
				!symbol.getStorage().isMemoryStorage()) {
				continue;
			}
			DataType type = E200Integers.of(variable);
			if (type != null && !Undefined.isUndefined(type)) {
				Address addr = symbol.getStorage().getMinAddress();
				Data data = listing.getDefinedDataAt(addr);
				int expectedSize = data != null ? data.getLength() : symbol.getSize();
				if (type.getLength() == expectedSize || (data == null && symbol.getSize() <= 1)) {
					uses.add(new Use(addr, type, type.getLength(), Access.VALUE));
				}
			}
		}
		AddressSpace space = program.getAddressFactory().getDefaultAddressSpace();
		long max = space.getMaxAddress().getOffset();
		Iterator<PcodeOpAST> ops = high.getPcodeOps();
		while (ops.hasNext()) {
			PcodeOpAST op = ops.next();
			int opcode = op.getOpcode();
			if (opcode == PcodeOp.PTRSUB && op.getInput(0).isConstant() &&
				op.getInput(0).getOffset() == 0 && op.getInput(1).isConstant()) {
				// the address of a global, used as a pointer: to itself or to the cast type
				long target = op.getInput(1).getOffset();
				if (target > 0 && target <= max) {
					for (DataType type : pointedTo(high, op.getOutput())) {
						uses.add(new Use(space.getAddress(target), type, type.getLength(),
							Access.ADDRESS));
					}
				}
				continue;
			}
			if (opcode == PcodeOp.CALL) {
				// a constant that is an address, passed where a pointer to a type is expected,
				// as f((ushort *)0x40001234) where nothing is defined at the address yet
				Function callee = E200Code.callee(functions, op);
				for (int i = 1; callee != null && i < op.getNumInputs() &&
					i - 1 < callee.getParameterCount(); i++) {
					Varnode arg = op.getInput(i);
					for (int depth = 0; arg != null && !arg.isConstant() && depth < 3; depth++) {
						PcodeOp def = arg.getDef();
						arg = def != null && (def.getOpcode() == PcodeOp.CAST ||
							def.getOpcode() == PcodeOp.COPY) ? def.getInput(0) : null;
					}
					if (arg != null && arg.isConstant()) { // not the address of a symbol
						Address address = E200Code.addressOf(program, arg, 0);
						DataType parameter = callee.getParameter(i - 1).getDataType();
						if (address != null && pointsToValue(parameter)) {
							DataType type = ((Pointer) parameter).getDataType();
							uses.add(new Use(address, type, type.getLength(), Access.ADDRESS));
						}
					}
				}
				continue;
			}
			if (opcode != PcodeOp.LOAD && opcode != PcodeOp.STORE) {
				continue;
			}
			Varnode value = opcode == PcodeOp.LOAD ? op.getOutput() : op.getInput(2);
			long base = constantBase(op.getInput(1), 0);
			if (value == null || base <= 0 || base > max) {
				continue;
			}
			uses.add(new Use(space.getAddress(base), E200Integers.of(value.getHigh()),
				value.getSize(), Access.INDEXED));
		}
		return uses;
	}

	/** The globals a decompiled function reads or writes with an undefined type */
	static List<Address> untyped(HighFunction high) {
		List<Address> untyped = new ArrayList<>();
		Iterator<HighSymbol> it = high.getGlobalSymbolMap().getSymbols();
		while (it.hasNext()) {
			HighSymbol symbol = it.next();
			HighVariable variable = symbol.getHighVariable();
			if (variable != null && symbol.getStorage() != null &&
				symbol.getStorage().isMemoryStorage() &&
				Undefined.isUndefined(variable.getDataType())) {
				untyped.add(symbol.getStorage().getMinAddress());
			}
		}
		return untyped;
	}

	/**
	 * The types a pointer points to, as its own type, the types it is cast to, and callee
	 * parameter types where passed as an argument, for numbers or pointers of 1, 2, 4 or 8
	 * bytes.
	 */
	private static List<DataType> pointedTo(HighFunction high, Varnode pointer) {
		FunctionManager functions = high.getFunction().getProgram().getFunctionManager();
		List<DataType> types = new ArrayList<>();
		Set<Varnode> visited = new HashSet<>();
		Deque<Varnode> queue = new ArrayDeque<>();
		queue.add(pointer);
		visited.add(pointer);
		while (!queue.isEmpty()) {
			Varnode v = queue.removeFirst();
			HighVariable hv = v.getHigh();
			if (hv != null && pointsToValue(hv.getDataType())) {
				types.add(((Pointer) hv.getDataType()).getDataType());
			}
			Iterator<PcodeOp> uses = v.getDescendants();
			while (uses.hasNext()) {
				PcodeOp use = uses.next();
				int opcode = use.getOpcode();
				if ((opcode == PcodeOp.CAST || opcode == PcodeOp.COPY || opcode == PcodeOp.PTRADD ||
					opcode == PcodeOp.MULTIEQUAL) && use.getOutput() != null) {
					if (visited.add(use.getOutput())) {
						queue.add(use.getOutput());
					}
				}
				else if (opcode == PcodeOp.CALL) {
					Function callee = E200Code.callee(functions, use);
					for (int i = 1; callee != null && i < use.getNumInputs(); i++) {
						if (use.getInput(i) == v && i - 1 < callee.getParameterCount()) {
							DataType parameter = callee.getParameter(i - 1).getDataType();
							if (pointsToValue(parameter)) {
								types.add(((Pointer) parameter).getDataType());
							}
						}
					}
				}
			}
		}
		return types;
	}

	/**
	 * Whether a type is a pointer to a number or pointer of 1, 2, 4 or 8 bytes, undefined
	 * ones included, or to a structure the analyzer created
	 */
	private static boolean pointsToValue(DataType type) {
		if (!(type instanceof Pointer p) || p.getDataType() == null) {
			return false;
		}
		DataType target = p.getDataType();
		int length = target.getLength();
		return E200Types.ownStructure(target) ||
			(E200Types.kind(target) != E200Types.Kind.OTHER || Undefined.isUndefined(target)) &&
				(length == 1 || length == 2 || length == 4 || length == 8);
	}

	/**
	 * The constant in an address computed as a constant plus an index, as in
	 * {@code i * 2 + 0x4000b020} or {@code (&DAT_4000b020)[i]}, or -1.
	 */
	private static long constantBase(Varnode address, int depth) {
		PcodeOp def = address == null || depth > 3 ? null : address.getDef();
		if (def == null) {
			return -1;
		}
		switch (def.getOpcode()) {
			case PcodeOp.INT_ADD: {
				Varnode a = def.getInput(0);
				Varnode b = def.getInput(1);
				if (a.isConstant() != b.isConstant()) {
					return (a.isConstant() ? a : b).getOffset();
				}
				long base = constantBase(a, depth + 1);
				return base >= 0 ? base : constantBase(b, depth + 1);
			}
			case PcodeOp.PTRSUB: // the address of a global, &DAT_...
				return def.getInput(0).isConstant() && def.getInput(0).getOffset() == 0 &&
					def.getInput(1).isConstant() ? def.getInput(1).getOffset() : -1;
			case PcodeOp.PTRADD: // an element of it, (&DAT_...)[i]
			case PcodeOp.CAST:
			case PcodeOp.COPY:
				return constantBase(def.getInput(0), depth + 1);
			default:
				return -1;
		}
	}

	// ---- A round of typing --------------------------------------------------------------------

	/**
	 * What the uses of the typable globals show in a round of typing. Only the globals that
	 * the analyzed functions and their callers use are typed; the other decompiled functions
	 * are there for the other uses of these globals.
	 */
	static final class Round {
		private final Program program;
		private final Listing listing;
		/** The globals that may be typed */
		final Set<Address> typable = new HashSet<>();
		/** The types of the uses of undefined data, by address */
		final Map<Address, List<DataType>> types = new HashMap<>();
		/** The facts of the decompiled functions, with the types of the elements of arrays */
		final List<E200TypeFlow.Facts> facts = new ArrayList<>();
		/** The uses of addresses where there is no data */
		private final Map<Address, List<Use>> undefined = new TreeMap<>();
		/** Addresses used as pointers to a type of another size than the undefined data there */
		private final Map<Address, List<Use>> mismatched = new TreeMap<>();
		/** Undefined data that code accesses as it is, typed or not */
		private final Set<Address> accessedAsIs = new HashSet<>();
		/** Addresses passed as pointers to a structure of the analyzer's */
		private final Map<Address, Structure> structures = new HashMap<>();
		private final Set<Address> conflicting = new HashSet<>();
		/** The types of the elements of arrays, for the default types */
		private final E200TypeFlow.Facts elements = new E200TypeFlow.Facts();

		/**
		 * @param results the decompiled functions
		 * @param functions the analyzed functions and their callers, whose globals are typed
		 */
		Round(Program program, Collection<E200DataTypes.Result> results,
				Set<Function> functions) {
			this.program = program;
			this.listing = program.getListing();
			for (E200DataTypes.Result result : results) {
				if (functions.contains(result.function())) {
					for (Use use : result.uses()) {
						typable.add(use.address());
					}
					typable.addAll(result.facts().globals());
					for (Map.Entry<E200TypeFlow.Slot, Address> p : result.facts().pointees) {
						typable.add(p.getValue());
					}
				}
			}
			facts.add(elements);
			for (E200DataTypes.Result result : results) {
				facts.add(result.facts());
				for (Use use : result.uses()) {
					if (typable.contains(use.address())) {
						add(use);
					}
				}
			}
			// undefined data of another size than the pointer's target, as the reference
			// analysis makes of an address an instruction only forms, is replaced where nothing
			// accesses the data as it is: a byte that code reads and a function writes as a
			// halfword with its complement stays a byte, for the structure of the pieces
			for (Map.Entry<Address, List<Use>> e : mismatched.entrySet()) {
				if (!accessedAsIs.contains(e.getKey()) && !types.containsKey(e.getKey()) &&
					!accessed(e.getKey())) {
					undefined.computeIfAbsent(e.getKey(), a -> new ArrayList<>())
							.addAll(e.getValue());
				}
			}
		}

		private void add(Use use) {
			if (use.access() == Access.ADDRESS && E200Types.ownStructure(use.type())) {
				Structure s = (Structure) use.type();
				if (structures.containsKey(use.address()) &&
					!structures.get(use.address()).isEquivalent(s)) {
					conflicting.add(use.address());
				}
				structures.put(use.address(), s);
				return;
			}
			Data data = listing.getDefinedDataAt(use.address());
			if (data == null) {
				undefined.computeIfAbsent(use.address(), a -> new ArrayList<>()).add(use);
				return;
			}
			// an array of undefined elements that code indexes is typed by the uses of its
			// first element, as one value of the element's size
			DataType type = data.getDataType();
			int length = data.getLength();
			if (type instanceof Array a && Undefined.isUndefined(a.getDataType())) {
				type = a.getDataType();
				length = a.getElementLength();
			}
			if (!Undefined.isUndefined(type)) {
				return;
			}
			if (use.access() == Access.ADDRESS && use.type() != null &&
				E200Types.informative(use.type()) && use.type().getLength() != length) {
				mismatched.computeIfAbsent(use.address(), a -> new ArrayList<>()).add(use);
			}
			else if (use.access() != Access.ADDRESS && use.size() == length) {
				accessedAsIs.add(use.address());
			}
			if (use.type() != null && use.type().getLength() == length) {
				if (!Undefined.isUndefined(use.type())) {
					types.computeIfAbsent(use.address(), a -> new ArrayList<>()).add(use.type());
				}
				if (use.access() == Access.INDEXED) {
					elements.type(new E200TypeFlow.Global(use.address()), use.type());
				}
			}
		}

		/** Whether an instruction reads or writes the data at an address */
		private boolean accessed(Address address) {
			for (Reference ref : program.getReferenceManager().getReferencesTo(address)) {
				if (ref.getReferenceType().isRead() || ref.getReferenceType().isWrite()) {
					return true;
				}
			}
			return false;
		}

		/**
		 * Gives the data that code passes as pointers to structures of the analyzer's those
		 * structures, where the passed structures agree; returns how many.
		 */
		int applyStructures(Set<Address> changed) {
			int applied = 0;
			for (Map.Entry<Address, Structure> e : structures.entrySet()) {
				if (!conflicting.contains(e.getKey()) &&
					E200Data.structureAt(program, e.getKey(), e.getValue())) {
					changed.add(e.getKey());
					applied++;
				}
			}
			return applied;
		}

		/**
		 * Creates data where code uses an address that has none: the start of arrays that code
		 * accesses at their address plus an index, and addresses that code uses as pointers to
		 * a type, such as a table in flash passed as a {@code short *}. The data is of the
		 * most frequent size of the accesses, and their types are added to the uses. Returns
		 * how many.
		 */
		int createData(Set<Address> changed) {
			Memory memory = program.getMemory();
			FunctionManager functions = program.getFunctionManager();
			int created = 0;
			for (Map.Entry<Address, List<Use>> e : undefined.entrySet()) {
				Address base = e.getKey();
				MemoryBlock block = memory.getBlock(base);
				// RAM or flash, not a peripheral, and not in the code of a function
				if (block == null || block.isVolatile() ||
					functions.getFunctionContaining(base) != null) {
					continue;
				}
				int size = E200Types.mostFrequent(e.getValue().stream().map(Use::size).toList());
				if (size != 1 && size != 2 && size != 4 && size != 8 ||
					base.getOffset() % size != 0) {
					continue;
				}
				try {
					Address end = base.addNoWrap(size - 1);
					if (!block.contains(end) || !onlyUndefined(base, end)) {
						continue;
					}
					listing.clearCodeUnits(base, end, false);
					listing.createData(base, Undefined.getUndefinedDataType(size));
				}
				catch (AddressOverflowException | CodeUnitInsertionException ex) {
					continue;
				}
				changed.add(base);
				created++;
				for (Use use : e.getValue()) {
					if (use.size() == size && use.type() != null &&
						!Undefined.isUndefined(use.type()) && use.type().getLength() == size) {
						types.computeIfAbsent(base, a -> new ArrayList<>()).add(use.type());
					}
					if (use.access() == Access.INDEXED && use.type() != null) {
						elements.type(new E200TypeFlow.Global(base), use.type());
					}
				}
			}
			return created;
		}

		/**
		 * Whether a range holds nothing but undefined bytes, data of undefined type that
		 * starts and ends within it, and stray instructions (data that was disassembled)
		 */
		private boolean onlyUndefined(Address start, Address end) {
			if (listing.isUndefined(start, end)) {
				return true;
			}
			AddressSet range = new AddressSet(start, end);
			if (!E200Data.strayCode(program, range)) {
				return false;
			}
			Instruction across = listing.getInstructionContaining(start);
			if (across != null && !across.getAddress().equals(start) ||
				(across = listing.getInstructionContaining(end)) != null &&
					across.getMaxAddress().compareTo(end) > 0) {
				return false; // an instruction that reaches out of the range
			}
			Data first = listing.getDataContaining(start);
			if (first != null && !first.getAddress().equals(start)) {
				return false;
			}
			for (Data d : listing.getDefinedData(range, true)) {
				DataType t = d.getDataType();
				if (!(t instanceof Undefined || t instanceof DefaultDataType) ||
					d.getMaxAddress().compareTo(end) > 0) {
					return false; // typed, or an array (of undefined values too)
				}
			}
			return true;
		}

		/**
		 * Gives the undefined globals the type their uses agree on (see the class comment);
		 * returns how many.
		 */
		int typeFromUses(Set<Address> changed, TaskMonitor monitor) throws CancelledException {
			boolean signedChar =
				program.getDataTypeManager().getDataOrganization().isSignedChar();
			int typed = 0;
			for (Map.Entry<Address, List<DataType>> e : types.entrySet()) {
				monitor.checkCancelled();
				DataType type = E200Types.chooseType(e.getValue(), signedChar, true);
				Data data = listing.getDefinedDataAt(e.getKey());
				if (type == null || data == null) {
					continue;
				}
				DataType replacement = null;
				if (Undefined.isUndefined(data.getDataType())) {
					replacement = type;
				}
				else if (data.getDataType() instanceof Array a &&
					Undefined.isUndefined(a.getDataType()) &&
					a.getElementLength() == type.getLength()) {
					// an array of undefined elements that code indexes: the type of its first
					// element, which code reads as a value too
					replacement = new ArrayDataType(type, a.getNumElements(), type.getLength(),
						program.getDataTypeManager());
				}
				if (replacement != null && E200Data.replace(listing, e.getKey(), replacement)) {
					changed.add(e.getKey());
					typed++;
				}
			}
			return typed;
		}
	}
}
