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

import ghidra.app.services.*;
import ghidra.app.util.importer.MessageLog;
import ghidra.framework.options.Options;
import ghidra.program.model.address.*;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * The analysis of the NXP e200z4 VLE language ({@code PowerPC:BE:32:VLE-e200}), in one
 * analyzer. It runs where Ghidra's constant reference analyzers run, on the code analysis
 * finds. At the start of each analysis, the first and every later one, it works out
 * <ul>
 * <li>the entry points of flash images ({@link E200EntryPoints})</li>
 * <li>the small data area bases r13 and r2 ({@link E200SmallDataBases})</li>
 * </ul>
 * and on all code, constant propagation with switch table recovery
 * ({@link E200ConstantPropagation}), again where the bases changed. It schedules the rest
 * after Decompiler Parameter ID, for the functions with code that is new or that the bases
 * changed, and every function it has not seen:
 * <ul>
 * <li>the MPC5746R peripherals ({@link E200Peripherals})</li>
 * <li>functions in gaps, calling conventions for kept registers and the signatures of
 * interrupt handlers ({@link E200Functions})</li>
 * <li>RAM blocks and the types of globals, parameters and return values
 * ({@link E200DataTypes})</li>
 * </ul>
 * An analysis ends with the data types step; code given to the analyzer after it, as when the
 * user disassembles more or runs the analyzer as one-shot analysis, starts the next.
 */
public class E200Analyzer extends AbstractAnalyzer {

	/** Language handled by this analyzer. */
	public static final String LANGUAGE_ID = "PowerPC:BE:32:VLE-e200";

	static final String NAME = "PowerPC e200";
	private static final String DESCRIPTION =
		"Analysis of NXP e200z4 VLE code (MPC57xx): entry points of flash images,\n" +
			"small data area bases and constant references, MPC5746R RAM and peripherals,\n" +
			"functions in gaps, calling conventions for kept registers, interrupt handler\n" +
			"signatures, and the types of globals, parameters and return values.";

	private final E200ConstantPropagation propagation = new E200ConstantPropagation();
	private final E200SmallDataBases smallDataBases = new E200SmallDataBases();
	private final E200EntryPoints entryPoints = new E200EntryPoints();
	private final E200Peripherals peripherals = new E200Peripherals();
	private final E200Functions functions = new E200Functions();
	private final E200DataTypes dataTypes = new E200DataTypes();

	private final Stage peripheralStage =
		new Stage(AnalysisPriority.DATA_TYPE_PROPOGATION.after().after(),
			(program, analyzed, monitor, log) -> peripherals.apply(program, monitor, log));
	// after Decompiler Parameter ID, which commits the prototypes the steps work with
	private final Stage functionStage = new Stage(
		AnalysisPriority.DATA_TYPE_PROPOGATION.after().after().after(), this::completeFunctions);
	private final Stage dataTypeStage =
		new Stage(AnalysisPriority.DATA_TYPE_PROPOGATION.after().after().after().after(),
			this::completeAnalysis);
	private final List<Stage> stages = List.of(peripheralStage, functionStage, dataTypeStage);

	/** Whether an analysis is under way: from the first code given to the data types step */
	private boolean analyzing;

	public E200Analyzer() {
		super(NAME, DESCRIPTION, AnalyzerType.INSTRUCTION_ANALYZER);
		setPriority(propagation.getPriority());
		setDefaultEnablement(true);
		setSupportsOneTimeAnalysis();
	}

	@Override
	public boolean canAnalyze(Program program) {
		return propagation.canAnalyze(program);
	}

	@Override
	public void registerOptions(Options options, Program program) {
		propagation.registerOptions(options, program);
		smallDataBases.registerOptions(options);
		entryPoints.registerOptions(options);
		peripherals.registerOptions(options);
		functions.registerOptions(options);
		dataTypes.registerOptions(options);
	}

	@Override
	public void optionsChanged(Options options, Program program) {
		propagation.optionsChanged(options, program);
		smallDataBases.optionsChanged(options);
		entryPoints.optionsChanged(options);
		peripherals.optionsChanged(options);
		functions.optionsChanged(options);
		dataTypes.optionsChanged(options);
	}

	@Override
	public boolean added(Program program, AddressSetView set, TaskMonitor monitor, MessageLog log)
			throws CancelledException {
		AddressSet code = new AddressSet(set);
		if (!analyzing) {
			analyzing = true;
			entryPoints.find(program, monitor);
			code.add(E200ConstantPropagation.forget(program,
				smallDataBases.update(program, monitor), monitor));
		}
		boolean ok = propagation.added(program, code, monitor, log);
		for (Stage stage : stages) {
			stage.schedule(program, code);
		}
		return ok;
	}

	/** The functions step; when it finds functions in gaps, it runs again for them. */
	private boolean completeFunctions(Program program, Set<Function> analyzed,
			TaskMonitor monitor, MessageLog log) throws CancelledException {
		boolean ok = functions.apply(program, analyzed, monitor, log);
		if (functions.foundFunctions()) {
			// created after this step, and then given prototypes by Decompiler Parameter ID
			functionStage.schedule(program, new AddressSet());
			dataTypeStage.schedule(program, new AddressSet());
		}
		return ok;
	}

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

	/** The data types step, which ends the analysis */
	private boolean completeAnalysis(Program program, Set<Function> analyzed, TaskMonitor monitor,
			MessageLog log) throws CancelledException {
		try {
			return dataTypes.apply(program, analyzed, monitor);
		}
		finally {
			analyzing = false;
		}
	}

	/** The work of a stage, for the functions it has not handled yet. */
	private interface Step {
		boolean apply(Program program, Set<Function> analyzed, TaskMonitor monitor,
				MessageLog log) throws CancelledException;
	}

	/**
	 * A step that runs later in analysis, at its own priority, scheduled as one-time analysis
	 * under the name of this analyzer. It handles the functions with code the analyzer was
	 * given since the step last ran, new code or code whose small data area bases changed, and
	 * the functions it has not seen before, such as those created on existing code.
	 */
	private static final class Stage extends AbstractAnalyzer {
		private final Step step;
		/** The entry points of the functions the step has seen */
		private final Set<Address> seen = new HashSet<>();
		private final AddressSet requested = new AddressSet();
		private boolean scheduled;

		Stage(AnalysisPriority priority, Step step) {
			super(NAME, DESCRIPTION, AnalyzerType.FUNCTION_ANALYZER);
			setPriority(priority);
			this.step = step;
		}

		void schedule(Program program, AddressSetView set) {
			requested.add(set);
			if (!scheduled) {
				scheduled = true;
				AutoAnalysisManager.getAnalysisManager(program)
						.scheduleOneTimeAnalysis(this, program.getMemory());
			}
		}

		@Override
		public boolean canAnalyze(Program program) {
			return true;
		}

		@Override
		public void optionsChanged(Options options, Program program) {
			// the options are those of the analyzer
		}

		@Override
		public boolean added(Program program, AddressSetView set, TaskMonitor monitor,
				MessageLog log) throws CancelledException {
			scheduled = false;
			Set<Function> analyzed = new HashSet<>();
			for (Function f : program.getFunctionManager().getFunctions(true)) {
				monitor.checkCancelled();
				boolean unseen = seen.add(f.getEntryPoint());
				if (!f.isThunk() && (unseen || f.getBody().intersects(requested))) {
					analyzed.add(f);
				}
			}
			requested.clear();
			return step.apply(program, analyzed, monitor, log);
		}
	}
}
