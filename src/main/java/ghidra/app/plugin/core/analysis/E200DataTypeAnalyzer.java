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

import ghidra.app.decompiler.*;
import ghidra.app.decompiler.parallel.DecompilerCallback;
import ghidra.app.decompiler.parallel.ParallelDecompiler;
import ghidra.app.services.*;
import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.data.*;
import ghidra.program.model.data.Enum;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Gives global data of undefined type ({@code undefined1}, {@code undefined2},
 * {@code undefined4}, {@code undefined8}) the type the decompiler infers from the functions
 * that use it, for the NXP e200z4 VLE language ({@code PowerPC:BE:32:VLE-e200}).
 * <p>
 * The reference analysis creates such data wherever code loads or stores a global, knowing
 * only the access size. The decompiler usually knows more: a value used by {@code efs*}
 * instructions is a {@code float}, one that is sign extended is signed, one that is
 * dereferenced is a pointer. A type is committed only when all uses agree, except that a
 * {@code float} use wins over integer uses of the same size (values that are only copied
 * look like integers) and integer uses that differ only in signedness go to a clear
 * majority. Single bytes get {@code byte} or {@code sbyte} rather than a character type.
 */
public class E200DataTypeAnalyzer extends AbstractAnalyzer {

	private static final String NAME = "PowerPC e200 Global Data Types";
	private static final String DESCRIPTION =
		"Gives global data of undefined type (undefined1, undefined2, undefined4 ...) the type\n" +
			"the decompiler infers from the functions that use it, such as float, ushort or\n" +
			"int, when those uses agree.";

	private static final int DECOMPILER_TIMEOUT_SECONDS = 60;


	/** A global variable use seen by the decompiler: its address and the inferred type. */
	private record Use(Address address, DataType type) {}

	public E200DataTypeAnalyzer() {
		super(NAME, DESCRIPTION, AnalyzerType.FUNCTION_ANALYZER);
		// after Decompiler Parameter ID, whose prototypes give the decompiler more to go on
		setPriority(AnalysisPriority.DATA_TYPE_PROPOGATION.after().after().after());
		setDefaultEnablement(true);
		setSupportsOneTimeAnalysis();
	}

	@Override
	public boolean canAnalyze(Program program) {
		return E200AddressAnalyzer.LANGUAGE_ID.equals(program.getLanguageID().getIdAsString());
	}

	@Override
	public boolean added(Program program, AddressSetView set, TaskMonitor monitor,
			MessageLog log) throws CancelledException {

		Set<Function> functions = new HashSet<>();
		for (Function f : program.getFunctionManager().getFunctions(set, true)) {
			if (!f.isThunk() && !f.isExternal()) {
				functions.add(f);
			}
		}
		if (functions.isEmpty()) {
			return true;
		}

		try {
			monitor.setMessage(NAME + " - decompiling");
			Map<Address, List<DataType>> uses = new HashMap<>();
			collectUses(program, functions, uses, monitor);

			// A type is only committed when all uses agree, so also look at the uses in
			// functions outside the analyzed set.
			Set<Function> others = new HashSet<>();
			for (Address addr : uses.keySet()) {
				for (Reference ref : program.getReferenceManager().getReferencesTo(addr)) {
					Function f = program.getFunctionManager()
							.getFunctionContaining(ref.getFromAddress());
					if (f != null && !f.isThunk() && !functions.contains(f)) {
						others.add(f);
					}
				}
			}
			if (!others.isEmpty()) {
				Map<Address, List<DataType>> otherUses = new HashMap<>();
				collectUses(program, others, otherUses, monitor);
				otherUses.forEach((addr, types) -> {
					List<DataType> list = uses.get(addr);
					if (list != null) {
						list.addAll(types);
					}
				});
			}

			monitor.setMessage(NAME + " - applying");
			int typed = 0;
			for (Map.Entry<Address, List<DataType>> e : uses.entrySet()) {
				monitor.checkCancelled();
				DataType type = chooseType(e.getValue(),
					program.getDataTypeManager().getDataOrganization().isSignedChar());
				if (type != null && applyType(program, e.getKey(), type)) {
					typed++;
				}
			}
			if (typed > 0) {
				Msg.info(this, "Typed " + typed + " global variables from their uses");
			}
		}
		catch (CancelledException | InterruptedException e) {
			throw new CancelledException();
		}
		catch (Exception e) {
			Msg.error(this, "Global data type inference failed", e);
		}
		return true;
	}

	/**
	 * Decompiles the functions and adds the inferred type of each global variable they use
	 * whose data is of undefined type.
	 */
	private void collectUses(Program program, Collection<Function> functions,
			Map<Address, List<DataType>> uses, TaskMonitor monitor) throws Exception {

		DecompilerCallback<List<Use>> callback =
			new DecompilerCallback<>(program, decompiler -> {
				DecompileOptions options = new DecompileOptions();
				options.grabFromProgram(program);
				decompiler.setOptions(options);
				decompiler.toggleCCode(false);
				decompiler.toggleSyntaxTree(true);
				decompiler.setSimplificationStyle("decompile");
			}) {
				@Override
				public List<Use> process(DecompileResults results, TaskMonitor m) {
					return globalUses(results);
				}
			};
		callback.setTimeout(DECOMPILER_TIMEOUT_SECONDS);
		List<List<Use>> results;
		try {
			results = ParallelDecompiler.decompileFunctions(callback, functions, monitor);
		}
		finally {
			callback.dispose();
		}

		Listing listing = program.getListing();
		for (List<Use> list : results) {
			if (list == null) {
				continue;
			}
			for (Use use : list) {
				Data data = listing.getDefinedDataAt(use.address());
				if (data != null && Undefined.isUndefined(data.getDataType())) {
					uses.computeIfAbsent(use.address(), a -> new ArrayList<>()).add(use.type());
				}
			}
		}
	}

	private static List<Use> globalUses(DecompileResults results) {
		HighFunction high = results.getHighFunction();
		if (high == null) {
			return null;
		}
		List<Use> uses = new ArrayList<>();
		Iterator<HighSymbol> it = high.getGlobalSymbolMap().getSymbols();
		while (it.hasNext()) {
			HighSymbol symbol = it.next();
			HighVariable variable = symbol.getHighVariable();
			if (variable == null || symbol.getStorage() == null ||
				!symbol.getStorage().isMemoryStorage()) {
				continue;
			}
			DataType type = variable.getDataType();
			if (type != null && !Undefined.isUndefined(type) &&
				type.getLength() == symbol.getSize()) {
				uses.add(new Use(symbol.getStorage().getMinAddress(), type));
			}
		}
		return uses;
	}

	private enum Kind {
		FLOAT, INTEGER, POINTER, OTHER
	}

	private static Kind kind(DataType type) {
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
	 * Chooses the type for a global from the types its uses were given, or returns null
	 * when they disagree.
	 *
	 * @param types the types of the uses
	 * @param signedChar whether plain {@code char} is signed in the program
	 * @return the type or null
	 */
	static DataType chooseType(List<DataType> types, boolean signedChar) {
		Map<String, DataType> distinct = new LinkedHashMap<>();
		Map<String, Integer> counts = new HashMap<>();
		for (DataType type : types) {
			if (kind(type) == Kind.OTHER) {
				return null;
			}
			String key = type.getPathName() + "/" + type.getLength();
			distinct.putIfAbsent(key, type);
			counts.merge(key, 1, Integer::sum);
		}
		DataType chosen = null;
		if (distinct.size() == 1) {
			chosen = distinct.values().iterator().next();
		}
		else if (!distinct.isEmpty()) {
			int length = -1;
			List<DataType> floats = new ArrayList<>();
			for (DataType type : distinct.values()) {
				if (length >= 0 && type.getLength() != length) {
					return null;
				}
				length = type.getLength();
				switch (kind(type)) {
					case FLOAT -> floats.add(type);
					case INTEGER -> {
						// copies and bit tests of a value look like integer uses
					}
					default -> {
						return null;
					}
				}
			}
			if (floats.size() == 1) {
				chosen = floats.get(0);
			}
			else if (floats.isEmpty()) {
				// integers that differ in signedness: the clear majority
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
				if (tie) {
					return null;
				}
			}
		}
		if (chosen instanceof CharDataType && chosen.getLength() == 1) {
			// single bytes in firmware are numbers, not characters
			boolean signed = chosen instanceof SignedCharDataType ||
				(!(chosen instanceof UnsignedCharDataType) && signedChar);
			chosen = signed ? SignedByteDataType.dataType : ByteDataType.dataType;
		}
		return chosen;
	}

	private static boolean applyType(Program program, Address addr, DataType type) {
		Listing listing = program.getListing();
		Data data = listing.getDefinedDataAt(addr);
		if (data == null || !Undefined.isUndefined(data.getDataType()) ||
			data.getLength() != type.getLength()) {
			return false;
		}
		try {
			listing.clearCodeUnits(addr, data.getMaxAddress(), false);
			listing.createData(addr, type);
			return true;
		}
		catch (CodeUnitInsertionException e) {
			try {
				listing.createData(addr, data.getDataType());
			}
			catch (CodeUnitInsertionException e2) {
				// the original undefined data could not be restored; leave the bytes
			}
			return false;
		}
	}
}
