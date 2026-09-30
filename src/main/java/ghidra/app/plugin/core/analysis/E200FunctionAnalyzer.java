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

import ghidra.app.services.*;
import ghidra.app.util.importer.MessageLog;
import ghidra.framework.options.Options;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.listing.Program;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Completes the functions after Decompiler Parameter ID:
 * <ul>
 * <li>creates the functions in gaps between functions, which nothing calls directly and which
 * have no stack frame (see {@link E200CodeGaps})</li>
 * <li>gives functions that keep some of the volatile registers, where their callers rely on
 * it, a calling convention that lists them (see {@link E200KeptRegisters})</li>
 * </ul>
 */
public class E200FunctionAnalyzer extends AbstractAnalyzer {

	private static final String NAME = "PowerPC e200 Functions";
	private static final String DESCRIPTION =
		"Creates the functions in gaps between functions (leaf functions without a stack frame\n" +
			"that nothing calls directly, such as getters and table lookup routines), and gives\n" +
			"functions that keep some of the volatile registers r0 and r3-r12, where their\n" +
			"callers rely on it, a calling convention that lists them.";

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

	private boolean gapsOption = true;
	private boolean keptOption = true;

	public E200FunctionAnalyzer() {
		super(NAME, DESCRIPTION, AnalyzerType.FUNCTION_ANALYZER);
		// after Decompiler Parameter ID, which commits the parameters that the calling
		// conventions may then keep (see E200KeptRegisters); the functions found in gaps get
		// their prototypes when Parameter ID and this analyzer run again for them. Before the
		// data type analysis, which then decompiles with the conventions.
		setPriority(AnalysisPriority.DATA_TYPE_PROPOGATION.after().after().after());
		setDefaultEnablement(true);
		setSupportsOneTimeAnalysis();
	}

	@Override
	public boolean canAnalyze(Program program) {
		return E200AddressAnalyzer.LANGUAGE_ID.equals(program.getLanguageID().getIdAsString());
	}

	@Override
	public void registerOptions(Options options, Program program) {
		options.registerOption(OPTION_NAME_GAPS, gapsOption, null, OPTION_DESCRIPTION_GAPS);
		options.registerOption(OPTION_NAME_KEPT, keptOption, null, OPTION_DESCRIPTION_KEPT);
	}

	@Override
	public void optionsChanged(Options options, Program program) {
		gapsOption = options.getBoolean(OPTION_NAME_GAPS, gapsOption);
		keptOption = options.getBoolean(OPTION_NAME_KEPT, keptOption);
	}

	@Override
	public boolean added(Program program, AddressSetView set, TaskMonitor monitor,
			MessageLog log) throws CancelledException {
		if (gapsOption) {
			// the functions are created after this pass; the analyzers run again for them
			E200CodeGaps.findFunctions(program, set, monitor);
		}
		if (keptOption) {
			return E200KeptRegisters.apply(program, monitor, log, NAME);
		}
		return true;
	}
}
