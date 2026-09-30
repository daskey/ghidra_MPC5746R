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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import ghidra.app.util.importer.MessageLog;
import ghidra.framework.options.Options;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.data.VoidDataType;
import ghidra.program.model.lang.Language;
import ghidra.program.model.listing.*;
import ghidra.program.model.listing.Function.FunctionUpdateType;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.symbol.FlowType;
import ghidra.program.model.symbol.SourceType;
import ghidra.util.Msg;
import ghidra.util.exception.*;
import ghidra.util.task.TaskMonitor;

/**
 * Completes the functions after Decompiler Parameter ID (part of {@link E200Analyzer}):
 * <ul>
 * <li>creates the functions in gaps between functions, which nothing calls directly and which
 * have no stack frame (see {@link E200CodeGaps})</li>
 * <li>gives functions that keep some of the volatile registers, where their callers rely on
 * it, a calling convention that lists them (see {@link E200KeptRegisters})</li>
 * <li>gives interrupt handlers, the functions that return only with an interrupt return such
 * as {@code se_rfi}, the signature {@code void f(void)}</li>
 * </ul>
 */
final class E200Functions {

	private static final String OPTION_NAME_GAPS = "Find functions in gaps";
	private static final String OPTION_DESCRIPTION_GAPS =
		"Create functions in a gap of undefined bytes and instructions of no function after a\n" +
			"function's return or unconditional branch, when all of it decodes as complete VLE\n" +
			"subroutines (apart from se_nop or erased padding).";
	private static final String OPTION_NAME_KEPT = "Calling conventions for kept registers";
	private static final String OPTION_DESCRIPTION_KEPT =
		"Give a function that keeps some of the volatile registers r0 and r3-r12, when a caller\n" +
			"reads one of them after the call, a calling convention that lists them as\n" +
			"unaffected (__keeps_r6_r8to12 and so on). Without it the decompiler shows the\n" +
			"values callers keep in those registers across the call as extraout_ variables.";
	private static final String OPTION_NAME_HANDLERS = "Signatures of interrupt handlers";
	private static final String OPTION_DESCRIPTION_HANDLERS =
		"Give the functions that return only with an interrupt return (se_rfi, se_rfci, ...)\n" +
			"the signature void f(void), unless the user set it. Handlers restore r3 and r4\n" +
			"before returning, which Decompiler Parameter ID takes for parameters and a result.";

	private boolean gapsOption = true;
	private boolean keptOption = true;
	private boolean handlersOption = true;

	/** Whether the last run found functions in gaps */
	private boolean found;

	void registerOptions(Options options) {
		options.registerOption(OPTION_NAME_GAPS, gapsOption, null, OPTION_DESCRIPTION_GAPS);
		options.registerOption(OPTION_NAME_KEPT, keptOption, null, OPTION_DESCRIPTION_KEPT);
		options.registerOption(OPTION_NAME_HANDLERS, handlersOption, null,
			OPTION_DESCRIPTION_HANDLERS);
	}

	void optionsChanged(Options options) {
		gapsOption = options.getBoolean(OPTION_NAME_GAPS, gapsOption);
		keptOption = options.getBoolean(OPTION_NAME_KEPT, keptOption);
		handlersOption = options.getBoolean(OPTION_NAME_HANDLERS, handlersOption);
	}

	/**
	 * Completes the functions, which Decompiler Parameter ID has given prototypes; returns
	 * false if the program's specification cannot be extended with calling conventions.
	 */
	boolean apply(Program program, Set<Function> analyzed, TaskMonitor monitor,
			MessageLog log) throws CancelledException {
		found = false;
		if (gapsOption) {
			// the functions are created after this step, and it runs again for them
			AddressSet entries = new AddressSet();
			analyzed.forEach(f -> entries.add(f.getEntryPoint()));
			found = E200CodeGaps.findFunctions(program, entries, monitor) > 0;
		}
		boolean ok = true;
		Set<Function> identified = new HashSet<>();
		if (keptOption) {
			ok = E200KeptRegisters.apply(program, identified, monitor, log, E200Analyzer.NAME);
		}
		if (handlersOption) {
			// and those whose signatures Decompiler Parameter ID set again
			identified.addAll(analyzed);
			setHandlerSignatures(program, identified, monitor);
		}
		return ok;
	}

	/** Whether the last run found functions in gaps */
	boolean foundFunctions() {
		return found;
	}

	/**
	 * Gives the functions whose returns are all interrupt returns the signature
	 * {@code void f(void)}, unless the user or an import set it. An interrupt handler saves the
	 * registers of the interrupted code and restores them before returning, r3 and r4 too, so
	 * Decompiler Parameter ID takes their values for parameters and a returned
	 * {@code undefined8}.
	 */
	private static void setHandlerSignatures(Program program, Set<Function> functions,
			TaskMonitor monitor) throws CancelledException {
		Language language = program.getLanguage();
		Listing listing = program.getListing();
		int changed = 0;
		for (Function function : functions) {
			monitor.checkCancelled();
			if (!returnsFromInterrupt(language, listing, function) ||
				function.getSignatureSource().isHigherPriorityThan(SourceType.ANALYSIS) ||
				function.getParameterCount() == 0 &&
					VoidDataType.isVoidDataType(function.getReturnType())) {
				continue;
			}
			try {
				function.updateFunction(null,
					new ReturnParameterImpl(VoidDataType.dataType, program), List.of(),
					FunctionUpdateType.DYNAMIC_STORAGE_ALL_PARAMS, true, SourceType.ANALYSIS);
				changed++;
			}
			catch (InvalidInputException | DuplicateNameException e) {
				Msg.warn(E200Analyzer.class,
					"Could not set the signature of " + function + ": " + e);
			}
		}
		if (changed > 0) {
			Msg.info(E200Analyzer.class,
				"Set the signature of " + changed + " interrupt handlers to void f(void)");
		}
	}

	/**
	 * Whether all the returns of a function, and at least one, go through a
	 * returnFrom...Interrupt p-code operation
	 */
	private static boolean returnsFromInterrupt(Language language, Listing listing,
			Function function) {
		boolean found = false;
		for (Instruction instruction : listing.getInstructions(function.getBody(), true)) {
			FlowType flow = instruction.getFlowType();
			if (!flow.isTerminal() || flow.isCall()) {
				continue;
			}
			boolean interrupt = false;
			for (PcodeOp op : instruction.getPcode()) {
				interrupt |= op.getOpcode() == PcodeOp.CALLOTHER && language
						.getUserDefinedOpName((int) op.getInput(0).getOffset())
						.startsWith("returnFrom");
			}
			if (!interrupt) {
				return false;
			}
			found = true;
		}
		return found;
	}
}
