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

import ghidra.program.model.address.Address;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.InvalidNameException;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Pointers to functions in flash data (part of {@link E200DataTypes}).
 * <p>
 * Handlers are called through tables of pointers and through pointer fields of structures in
 * flash, as {@code PTR_ARRAY_090e07a4[mode]()} and {@code p->f10()}. The reference analysis
 * types such a pointer as a pointer to nothing in particular, so the decompiler shows the
 * calls as {@code (*(code *)PTR_ARRAY_090e07a4[mode])()}. A pointer, an element of an array
 * of pointers or a pointer field of a structure whose values in flash are all entry points of
 * functions (or null) gets a pointer to a function definition: the functions' signature where
 * they all have the same, otherwise one with their number of parameters and no types. The
 * decompiler then shows {@code (*PTR_ARRAY_090e07a4[mode])()}. The places whose values code
 * calls through, or that get the entry point of a function, are typed by {@link E200TypeFlow}
 * with the definitions of {@link Definitions}.
 */
final class E200FunctionPointers {

	/** Category of the function definitions */
	private static final CategoryPath CATEGORY = E200Tables.CATEGORY;
	/**
	 * Parameters a function pointed to may have: a hand-written routine that reads all the
	 * argument registers gets eight from Decompiler Parameter ID, and a definition with them
	 * would show the registers at every call through the pointer
	 */
	private static final int MAX_PARAMETERS = 6;

	private E200FunctionPointers() {
	}

	/**
	 * Types the pointers to functions in flash data; returns the number of data, array
	 * element types and structure fields typed.
	 */
	static int apply(Program program, TaskMonitor monitor) throws CancelledException {
		Listing listing = program.getListing();
		FunctionManager functions = program.getFunctionManager();
		DataTypeManager manager = program.getDataTypeManager();
		Definitions definitions = new Definitions(program);
		// the instances of each structure the analyzer made, in flash
		Map<Structure, List<Data>> instances = new LinkedHashMap<>();
		// the data to retype, after the iteration over the listing
		Map<Address, DataType> replacements = new LinkedHashMap<>();
		int typed = 0;
		for (MemoryBlock block : program.getMemory().getBlocks()) {
			if (!block.isInitialized() || block.isVolatile()) {
				continue;
			}
			DataIterator it = listing.getDefinedData(block.getStart(), true);
			while (it.hasNext()) {
				monitor.checkCancelled();
				Data data = it.next();
				if (data.getAddress().compareTo(block.getEnd()) > 0) {
					break;
				}
				DataType type = data.getDataType();
				if (type instanceof Array array) {
					DataType element = array.getDataType();
					if (E200Tables.ownStructure(element)) {
						for (int i = 0; i < data.getNumComponents(); i++) {
							instances.computeIfAbsent((Structure) element, s -> new ArrayList<>())
									.add(data.getComponent(i));
						}
					}
					else if (untypedPointer(element)) {
						List<Function> targets = new ArrayList<>();
						for (int i = 0; i < data.getNumComponents() && targets != null; i++) {
							targets = target(functions, data.getComponent(i), targets);
						}
						FunctionDefinition definition = definitions.forTargets(targets);
						if (definition != null) {
							replacements.put(data.getAddress(), new ArrayDataType(
								new PointerDataType(definition, 4, manager),
								array.getNumElements(), 4, manager));
						}
					}
				}
				else if (E200Tables.ownStructure(type)) {
					instances.computeIfAbsent((Structure) type, s -> new ArrayList<>()).add(data);
				}
				else if (untypedPointer(type)) {
					FunctionDefinition definition =
						definitions.forTargets(target(functions, data, new ArrayList<>()));
					if (definition != null) {
						replacements.put(data.getAddress(),
							new PointerDataType(definition, 4, manager));
					}
				}
			}
		}
		for (Map.Entry<Address, DataType> e : replacements.entrySet()) {
			monitor.checkCancelled();
			if (replace(listing, listing.getDefinedDataAt(e.getKey()), e.getValue())) {
				typed++;
			}
		}
		// fields of structures: all instances must agree
		for (Map.Entry<Structure, List<Data>> e : instances.entrySet()) {
			monitor.checkCancelled();
			Structure s = e.getKey();
			for (DataTypeComponent c : s.getDefinedComponents()) {
				if (!untypedPointer(c.getDataType()) && !untypedWord(c.getDataType())) {
					continue;
				}
				List<Function> targets = new ArrayList<>();
				for (Data instance : e.getValue()) {
					Data field = instance.getComponentContaining(c.getOffset());
					if (field == null || field.getParentOffset() != c.getOffset() ||
						field.getLength() != 4) {
						targets = null;
						break;
					}
					targets = target(functions, field, targets);
					if (targets == null) {
						break;
					}
				}
				FunctionDefinition definition = definitions.forTargets(targets);
				if (definition != null) {
					s.replaceAtOffset(c.getOffset(), new PointerDataType(definition, 4, manager),
						4, c.getFieldName(), c.getComment());
					typed++;
				}
			}
		}
		return typed;
	}

	/** A pointer to nothing in particular: to undefined, void or an integer */
	private static boolean untypedPointer(DataType type) {
		if (!(type instanceof Pointer p) || type.getLength() != 4) {
			return false;
		}
		DataType target = p.getDataType();
		return target == null || target instanceof DefaultDataType ||
			Undefined.isUndefined(target) || target instanceof VoidDataType ||
			target instanceof AbstractIntegerDataType;
	}

	/** An undefined or unsigned integer of 4 bytes */
	private static boolean untypedWord(DataType type) {
		return type.getLength() == 4 && (Undefined.isUndefined(type) &&
			!(type instanceof DefaultDataType) || type instanceof UnsignedIntegerDataType);
	}

	/**
	 * Adds the function a datum's value points to, to the list; null (a null pointer) adds
	 * nothing; returns null if the value is neither
	 */
	static List<Function> target(FunctionManager functions, Data data, List<Function> targets) {
		if (targets == null || data.getLength() != 4) {
			return null;
		}
		Object value = data.getValue();
		Address address = null;
		if (value instanceof Address a) {
			address = a;
		}
		else if (value instanceof Scalar s) {
			if (s.getUnsignedValue() == 0) {
				return targets;
			}
			address = data.getAddress().getNewAddress(s.getUnsignedValue());
		}
		if (address == null) {
			return null;
		}
		if (address.getOffset() == 0) {
			return targets;
		}
		Function f = functions.getFunctionAt(address);
		if (f == null) {
			return null;
		}
		targets.add(f.isThunk() ? f.getThunkedFunction(true) : f);
		return targets;
	}

	/**
	 * A call through a pointer: the sizes and the types of its arguments (null for a
	 * constant), and the size and type of its result if the result is used
	 */
	record Call(int[] sizes, DataType[] types, int resultSize, DataType resultType) {
		static Call of(PcodeOp call) {
			int n = call.getNumInputs() - 1;
			int[] sizes = new int[n];
			DataType[] types = new DataType[n];
			for (int i = 0; i < n; i++) {
				Varnode v = call.getInput(i + 1);
				sizes[i] = v.getSize();
				types[i] = v.isConstant() ? null : E200Integers.of(v);
			}
			Varnode out = call.getOutput();
			return new Call(sizes, types, out == null ? 0 : out.getSize(),
				out == null ? null : E200Integers.of(out));
		}

		boolean returns() {
			return resultSize > 0;
		}
	}

	/**
	 * The function definitions of the analyzer's category, one per prototype. For pointers
	 * to known functions, their signature if they all have one; otherwise, and for pointers
	 * code only calls through, one with the number of parameters most of the functions or
	 * calls have, each parameter typed as they agree, or as the unsigned integer of the size
	 * they agree on. A definition whose parameters are not the size of the arguments passed
	 * through the pointer is not used: the decompiler cannot pass a byte where the prototype
	 * says a word.
	 */
	static final class Definitions {
		private final Program program;
		private final DataTypeManager manager;
		private final boolean signedChar;
		private final Map<String, FunctionDefinition> byPrototype = new HashMap<>();

		Definitions(Program program) {
			this.program = program;
			this.manager = program.getDataTypeManager();
			this.signedChar = manager.getDataOrganization().isSignedChar();
			Category category = manager.getCategory(CATEGORY);
			if (category != null) {
				for (DataType t : category.getDataTypes()) {
					if (t instanceof FunctionDefinition d) {
						byPrototype.putIfAbsent(key(d), d);
					}
				}
			}
		}

		/**
		 * The definition for pointers to the functions; null if there are none, or no number
		 * of parameters is in the majority, or that number is implausible for C, or the
		 * functions with that number disagree on the size of a parameter or of the result
		 */
		FunctionDefinition forTargets(Collection<Function> targets) {
			if (targets == null || targets.isEmpty()) {
				return null;
			}
			List<Integer> counts = new ArrayList<>();
			for (Function f : targets) {
				counts.add(f.getParameterCount());
			}
			int parameterCount = E200DataTypes.mostFrequent(counts);
			if (parameterCount > MAX_PARAMETERS ||
				Collections.frequency(counts, parameterCount) * 2 <= targets.size() &&
					Collections.frequency(counts, parameterCount) < targets.size()) {
				return null;
			}
			Function first = null;
			boolean same = true;
			List<List<DataType>> parameters = new ArrayList<>();
			for (int i = 0; i < parameterCount; i++) {
				parameters.add(new ArrayList<>());
			}
			List<DataType> returns = new ArrayList<>();
			for (Function f : targets) {
				if (f.getParameterCount() != parameterCount) {
					same = false;
					continue;
				}
				if (first == null) {
					first = f;
				}
				else if (!first.getSignature().isEquivalentSignature(f.getSignature())) {
					same = false;
				}
				for (int i = 0; i < parameterCount; i++) {
					parameters.get(i).add(f.getParameter(i).getDataType());
				}
				returns.add(f.getReturnType());
			}
			if (same) {
				return add(new FunctionDefinitionDataType(CATEGORY,
					"F_" + first.getEntryPoint().toString(false), first.getSignature(), manager));
			}
			return definition(parameters, returns);
		}

		/**
		 * The definition for pointers that code calls through {@code calls}; null if the
		 * calls with the most frequent number of arguments disagree on the size of one, or
		 * of the result, or that number is implausible for C
		 */
		FunctionDefinition forCalls(Collection<Call> calls) {
			if (calls.isEmpty()) {
				return null;
			}
			List<Integer> counts = new ArrayList<>();
			for (Call c : calls) {
				counts.add(c.sizes().length);
			}
			int parameterCount = E200DataTypes.mostFrequent(counts);
			if (parameterCount > MAX_PARAMETERS) {
				return null;
			}
			List<List<DataType>> parameters = new ArrayList<>();
			for (int i = 0; i < parameterCount; i++) {
				parameters.add(new ArrayList<>());
			}
			List<DataType> returns = new ArrayList<>();
			boolean returns1 = false;
			for (Call c : calls) {
				if (c.sizes().length != parameterCount) {
					continue;
				}
				for (int i = 0; i < parameterCount; i++) {
					DataType t = c.types()[i];
					parameters.get(i).add(t != null && t.getLength() == c.sizes()[i] ? t
							: Undefined.getUndefinedDataType(c.sizes()[i]));
				}
				if (c.returns()) {
					returns1 = true;
					DataType t = c.resultType();
					returns.add(t != null && t.getLength() == c.resultSize() ? t
							: Undefined.getUndefinedDataType(c.resultSize()));
				}
			}
			if (!returns1) {
				returns.add(VoidDataType.dataType);
			}
			return definition(parameters, returns);
		}

		/**
		 * A definition with the parameters and the return type the lists agree on: the type
		 * if all agree, else the unsigned integer of the size if all have one size; null
		 * otherwise. Returns are void if all are, else the types of the others.
		 */
		private FunctionDefinition definition(List<List<DataType>> parameters,
				List<DataType> returns) {
			ParameterDefinition[] arguments = new ParameterDefinition[parameters.size()];
			for (int i = 0; i < arguments.length; i++) {
				DataType type = agreed(parameters.get(i));
				if (type == null) {
					return null;
				}
				arguments[i] = new ParameterDefinitionImpl(null, type, null);
			}
			List<DataType> values = new ArrayList<>();
			for (DataType t : returns) {
				if (t != null && !(t instanceof VoidDataType) && !(t instanceof DefaultDataType)) {
					values.add(t);
				}
			}
			DataType returned = values.isEmpty() ? VoidDataType.dataType : agreed(values);
			if (returned == null) {
				return null;
			}
			FunctionDefinitionDataType definition =
				new FunctionDefinitionDataType(CATEGORY, "F", manager);
			definition.setArguments(arguments);
			definition.setReturnType(returned);
			StringBuilder name = new StringBuilder("F_").append(typeName(returned));
			for (ParameterDefinition p : arguments) {
				name.append('_').append(typeName(p.getDataType()));
			}
			try {
				definition.setName(name.toString());
			}
			catch (InvalidNameException e) {
				return null;
			}
			return add(definition);
		}

		/**
		 * The type a list of types agrees on: the one they all are, or the unsigned integer
		 * of their size when they are all of one size of 1, 2, 4 or 8 bytes; null otherwise
		 */
		private DataType agreed(List<DataType> types) {
			if (types.isEmpty()) {
				return null;
			}
			int size = types.get(0).getLength();
			List<DataType> informative = new ArrayList<>();
			for (DataType t : types) {
				if (t == null || t.getLength() != size) {
					return null;
				}
				if (E200TypeFlow.informative(t)) {
					informative.add(t);
				}
			}
			DataType type = informative.size() == types.size()
					? E200DataTypes.chooseType(informative, signedChar, true)
					: null;
			return type != null ? type : E200DataTypes.unsigned(size);
		}

		private static String typeName(DataType t) {
			if (t instanceof Pointer p) {
				return (p.getDataType() == null ? "void" : typeName(p.getDataType())) + "_ptr";
			}
			return t.getName().replaceAll("[^A-Za-z0-9_]", "");
		}

		/**
		 * Whether a definition fits the calls through a pointer: the arguments it and a call
		 * have at the same position are of one size, and a call's result is one it returns,
		 * of its size
		 */
		static boolean fits(FunctionDefinition d, Collection<Call> calls) {
			ParameterDefinition[] arguments = d.getArguments();
			for (Call c : calls) {
				for (int i = 0; i < Math.min(arguments.length, c.sizes().length); i++) {
					if (arguments[i].getDataType().getLength() != c.sizes()[i]) {
						return false;
					}
				}
				if (c.returns() && (d.getReturnType() instanceof VoidDataType ||
					d.getReturnType().getLength() != c.resultSize())) {
					return false;
				}
			}
			return true;
		}

		/**
		 * The definition for a place that holds pointers to {@code targets} (the entry points
		 * of functions) or that code calls through ({@code calls}): from the functions where
		 * there are any, they agree and the calls fit, else from the calls; null if neither
		 * gives one
		 */
		FunctionDefinition of(Collection<Address> targets, Collection<Call> calls) {
			List<Function> functions = new ArrayList<>();
			for (Address a : targets) {
				Function f = program.getFunctionManager().getFunctionAt(a);
				if (f != null) {
					functions.add(f.isThunk() ? f.getThunkedFunction(true) : f);
				}
			}
			FunctionDefinition definition = forTargets(functions);
			if (definition != null && fits(definition, calls)) {
				return definition;
			}
			return forCalls(calls);
		}

		/** One definition per prototype, in the data type manager */
		private FunctionDefinition add(FunctionDefinitionDataType definition) {
			String key = key(definition);
			FunctionDefinition existing = byPrototype.get(key);
			if (existing == null) {
				try {
					definition.setName(manager.getUniqueName(CATEGORY, definition.getName()));
				}
				catch (InvalidNameException e) {
					return null;
				}
				existing = (FunctionDefinition) manager.addDataType(definition,
					DataTypeConflictHandler.DEFAULT_HANDLER);
				byPrototype.put(key, existing);
			}
			return existing;
		}

		private static String key(FunctionDefinition definition) {
			StringBuilder key = new StringBuilder(definition.getReturnType().getPathName());
			key.append(' ').append(definition.getCallingConventionName()).append('(');
			for (ParameterDefinition p : definition.getArguments()) {
				key.append(p.getDataType().getPathName()).append(',');
			}
			return key.toString();
		}
	}

	/** Replaces a datum with one of the given type; returns whether it did */
	private static boolean replace(Listing listing, Data data, DataType type) {
		if (data == null || type.getLength() != data.getLength()) {
			return false;
		}
		try {
			listing.clearCodeUnits(data.getAddress(), data.getMaxAddress(), false);
			listing.createData(data.getAddress(), type);
			return true;
		}
		catch (CodeUnitInsertionException e) {
			return false;
		}
	}
}
