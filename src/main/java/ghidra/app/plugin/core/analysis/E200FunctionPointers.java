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
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.util.CodeUnitInsertionException;
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
 * decompiler then shows {@code (*PTR_ARRAY_090e07a4[mode])()}.
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
		Map<String, FunctionDefinition> definitions = new HashMap<>();
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
						FunctionDefinition definition =
							definition(manager, definitions, targets);
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
					FunctionDefinition definition = definition(manager, definitions,
						target(functions, data, new ArrayList<>()));
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
				FunctionDefinition definition = definition(manager, definitions, targets);
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
	private static List<Function> target(FunctionManager functions, Data data,
			List<Function> targets) {
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
	 * The function definition for pointers to the functions: their signature if they all have
	 * one, else one with the number of parameters most of them have (the handlers in a table
	 * are called alike, and Decompiler Parameter ID gives one of them a parameter it reads
	 * but does not use) and undefined types; null if there are none, or no number of
	 * parameters is in the majority
	 */
	private static FunctionDefinition definition(DataTypeManager manager,
			Map<String, FunctionDefinition> definitions, List<Function> targets) {
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
		boolean returnsNothing = true;
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
			if (!(f.getReturnType() instanceof VoidDataType)) {
				returnsNothing = false;
			}
		}
		String name = manager.getUniqueName(CATEGORY, "F_" + first.getEntryPoint().toString(false));
		FunctionDefinitionDataType definition;
		if (same) {
			definition =
				new FunctionDefinitionDataType(CATEGORY, name, first.getSignature(), manager);
		}
		else {
			definition = new FunctionDefinitionDataType(CATEGORY, name, manager);
			ParameterDefinition[] parameters = new ParameterDefinition[parameterCount];
			for (int i = 0; i < parameters.length; i++) {
				parameters[i] = new ParameterDefinitionImpl(null,
					Undefined4DataType.dataType, null);
			}
			definition.setArguments(parameters);
			definition.setReturnType(
				returnsNothing ? VoidDataType.dataType : Undefined4DataType.dataType);
		}
		// one definition per prototype
		StringBuilder key = new StringBuilder(definition.getReturnType().getPathName());
		key.append(' ').append(definition.getCallingConventionName()).append('(');
		for (ParameterDefinition p : definition.getArguments()) {
			key.append(p.getDataType().getPathName()).append(',');
		}
		FunctionDefinition existing = definitions.get(key.toString());
		if (existing == null) {
			existing = (FunctionDefinition) manager.addDataType(definition,
				DataTypeConflictHandler.DEFAULT_HANDLER);
			definitions.put(key.toString(), existing);
		}
		return existing;
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
