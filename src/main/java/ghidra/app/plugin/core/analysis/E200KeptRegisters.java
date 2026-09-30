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

import java.io.StringReader;
import java.io.StringWriter;
import java.util.*;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.*;
import org.xml.sax.InputSource;

import ghidra.app.cmd.function.DecompilerParameterIdCmd;
import ghidra.app.util.importer.MessageLog;
import ghidra.framework.options.Options;
import ghidra.program.database.SpecExtension;
import ghidra.program.model.address.*;
import ghidra.program.model.lang.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.symbol.*;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Calling conventions for functions that keep some of the volatile registers r0 and r3-r12,
 * where a caller relies on it (part of {@link E200FunctionAnalyzer}).
 * <p>
 * The EABI lets a function change r0 and r3-r12, and Ghidra's calling convention says it does.
 * Compilers for the e200 know which registers the functions they compile change, and keep
 * values in the others across calls: a caller sets r6 to 0, calls a copy loop that changes only
 * r0 and r7, and then stores r6. The decompiler shows the value after the call as
 * {@code extraout_r6}, a result of the call, instead of 0.
 * <p>
 * The registers a function changes are the ones its instructions write and those the functions
 * it calls or branches to change. Indirect calls, unresolved computed jumps and flows to
 * anything but the entry of a function mean it can change all. Where a caller reads a register
 * the called function keeps, after the call and before writing it, the called function gets a
 * calling convention that lists the registers it keeps as unaffected, named after them, such as
 * {@code __keeps_r6_r8to12}. The conventions are added to the program as specification
 * extensions.
 * <p>
 * The decompiler names an input in an unaffected register {@code unaff_}, even a parameter,
 * unless it is a parameter of the function's committed signature. So registers a function
 * reads before writing them count as kept only if they hold such parameters, as Decompiler
 * Parameter ID commits them before this runs. Parameter ID runs again for the callers whose
 * view of a call changes, since it took the kept registers they read after the call for
 * results of the call. Functions with a signature set by the user, or a calling convention set
 * otherwise, are left alone.
 */
final class E200KeptRegisters {

	static final String PREFIX = "__keeps_";
	/** The volatile GPRs, in the order of the bits of a register mask. */
	static final String[] VOLATILE =
		{ "r0", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11", "r12" };
	static final int ALL = (1 << VOLATILE.length) - 1;
	/** Instructions followed after a call when looking for reads of the kept registers */
	private static final int MAX_STEPS = 256;
	/** Rounds of conventions and Decompiler Parameter ID for the callers they change */
	private static final int MAX_ROUNDS = 3;
	private static final String PARAMETER_ID = "Decompiler Parameter ID";

	private E200KeptRegisters() {
	}

	/**
	 * Sets the calling conventions; returns false if the program's specification cannot be
	 * extended, for example without exclusive access to a shared program.
	 * <p>
	 * Decompiler Parameter ID, which ran before, took the kept registers a function reads after
	 * a call for results of the call, and may have missed parameters. When it is enabled, it
	 * runs again for the callers of the functions whose convention changed, and the conventions
	 * are worked out again with their new signatures, a few rounds at most.
	 */
	static boolean apply(Program program, TaskMonitor monitor, MessageLog log, String source)
			throws CancelledException {
		int changed = 0;
		Set<String> added = new TreeSet<>();
		// what the instructions read and write does not depend on the signatures
		RegisterUse use = new RegisterUse(program, monitor);
		for (int round = 0; round < MAX_ROUNDS; round++) {
			Map<Function, Integer> needed = use.reliedOn(monitor);
			Set<Function> callers = new HashSet<>();
			for (Function function : program.getFunctionManager().getFunctions(true)) {
				monitor.checkCancelled();
				Integer kept = needed.get(function);
				String wanted = kept == null ? null : conventionName(kept);
				try {
					if (update(program, function, wanted, kept, added, monitor)) {
						changed++;
						callers.addAll(use.relyingCallers(function));
					}
				}
				catch (Exception e) {
					log.appendMsg(source, "Could not add calling convention " + wanted + ": " + e);
					return false;
				}
			}
			if (callers.isEmpty() || !identifyParameters(program, callers, monitor)) {
				break;
			}
		}
		if (changed > 0) {
			Msg.info(E200KeptRegisters.class, "Set the calling convention of " + changed +
				" functions that keep registers their callers use" +
				(added.isEmpty() ? "" : "; added " + String.join(", ", added)));
		}
		return true;
	}

	/**
	 * Gives the function the calling convention {@code wanted}, or the default one if null and
	 * it has one of these; returns whether it changed.
	 */
	private static boolean update(Program program, Function function, String wanted,
			Integer kept, Set<String> added, TaskMonitor monitor) throws Exception {
		String current = function.getCallingConventionName();
		boolean ours = current.startsWith(PREFIX);
		if (function.getSignatureSource() == SourceType.USER_DEFINED ||
			!ours && !current.equals(Function.UNKNOWN_CALLING_CONVENTION_STRING) &&
				!current.equals(Function.DEFAULT_CALLING_CONVENTION_STRING) &&
				!current.equals(program.getCompilerSpec().getDefaultCallingConvention().getName())) {
			return false; // set by the user or otherwise
		}
		if (wanted == null) {
			if (!ours) {
				return false;
			}
			setConvention(function, Function.DEFAULT_CALLING_CONVENTION_STRING);
			return true;
		}
		if (wanted.equals(current)) {
			return false;
		}
		if (program.getCompilerSpec().getCallingConvention(wanted) == null) {
			new SpecExtension(program).addReplaceCompilerSpecExtension(
				conventionXml(program, wanted, kept), monitor);
			added.add(wanted);
		}
		setConvention(function, wanted);
		return true;
	}

	/**
	 * Runs Decompiler Parameter ID for the functions, with its analysis options, if it is
	 * enabled; returns whether it ran.
	 */
	private static boolean identifyParameters(Program program, Set<Function> functions,
			TaskMonitor monitor) {
		Options analysis = program.getOptions(Program.ANALYSIS_PROPERTIES);
		if (!analysis.getBoolean(PARAMETER_ID, false)) {
			return false;
		}
		Options options = analysis.getOptions(PARAMETER_ID);
		AddressSet entries = new AddressSet();
		for (Function f : functions) {
			entries.add(f.getEntryPoint());
		}
		new DecompilerParameterIdCmd(PARAMETER_ID, entries,
			options.getEnum("Analysis Clear Level", SourceType.ANALYSIS),
			options.getBoolean("Commit Data Types", true),
			options.getBoolean("Commit Void Return Values", false),
			options.getInt("Analysis Decompiler Timeout (sec)", 60)).applyTo(program, monitor);
		return true;
	}

	private static void setConvention(Function function, String name) {
		try {
			function.setCallingConvention(name);
		}
		catch (Exception e) {
			Msg.warn(E200KeptRegisters.class,
				"Could not set the calling convention of " + function + ": " + e);
		}
	}

	/** {@code __keeps_r6_r8to12}: the kept registers, with runs of three or more joined */
	static String conventionName(int kept) {
		StringJoiner name = new StringJoiner("_", PREFIX, "");
		int i = 0;
		while (i < VOLATILE.length) {
			if ((kept & (1 << i)) == 0) {
				i++;
				continue;
			}
			int j = i;
			while (j + 1 < VOLATILE.length && (kept & (1 << (j + 1))) != 0 &&
				number(j + 1) == number(j) + 1) {
				j++;
			}
			name.add(j > i + 1 ? VOLATILE[i] + "to" + number(j)
					: j == i + 1 ? VOLATILE[i] + "_" + VOLATILE[j] : VOLATILE[i]);
			i = j + 1;
		}
		return name.toString();
	}

	private static int number(int index) {
		return Integer.parseInt(VOLATILE[index].substring(1));
	}

	/**
	 * The default calling convention, renamed, with the kept registers moved from the
	 * killed-by-call to the unaffected registers.
	 */
	static String conventionXml(Program program, String name, int kept) throws Exception {
		CompilerSpec cspec = program.getCompilerSpec();
		XmlEncode encoder = new XmlEncode();
		cspec.getDefaultCallingConvention().encode(encoder, cspec.getPcodeInjectLibrary());
		Document doc = DocumentBuilderFactory.newInstance()
				.newDocumentBuilder()
				.parse(new InputSource(new StringReader(encoder.toString())));
		Element prototype = doc.getDocumentElement();
		prototype.setAttribute("name", name);
		Element unaffected = child(doc, prototype, "unaffected");
		Element killed = child(doc, prototype, "killedbycall");
		Language language = program.getLanguage();
		for (Element list : List.of(unaffected, killed)) {
			for (Node n = list.getFirstChild(); n != null;) {
				Node next = n.getNextSibling();
				if (n instanceof Element e && volatileIndex(language, e) >= 0) {
					list.removeChild(n);
				}
				n = next;
			}
		}
		for (int i = 0; i < VOLATILE.length; i++) {
			Element register = doc.createElement("register");
			register.setAttribute("name", VOLATILE[i]);
			((kept & (1 << i)) != 0 ? unaffected : killed).appendChild(register);
		}
		var transformer = TransformerFactory.newInstance().newTransformer();
		transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
		StringWriter out = new StringWriter();
		transformer.transform(new DOMSource(doc), new StreamResult(out));
		return out.toString();
	}

	private static Element child(Document doc, Element parent, String tag) {
		NodeList list = parent.getElementsByTagName(tag);
		if (list.getLength() > 0) {
			return (Element) list.item(0);
		}
		Element e = doc.createElement(tag);
		parent.appendChild(e);
		return e;
	}

	/** The index in {@link #VOLATILE} of the register an element of a register list names. */
	private static int volatileIndex(Language language, Element e) {
		Register register = null;
		if (e.hasAttribute("name")) {
			register = language.getRegister(e.getAttribute("name"));
		}
		else if ("register".equals(e.getAttribute("space")) && e.hasAttribute("offset")) {
			long offset = Long.decode(e.getAttribute("offset"));
			int size = e.hasAttribute("size") ? Integer.decode(e.getAttribute("size")) : 4;
			register = language.getRegister(
				language.getAddressFactory().getRegisterSpace().getAddress(offset), size);
		}
		if (register == null) {
			return -1;
		}
		return Arrays.asList(VOLATILE).indexOf(register.getBaseRegister().getName());
	}

	/** Which volatile registers the instructions and functions of a program read and write. */
	static class RegisterUse {
		private final Listing listing;
		private final FunctionManager functions;
		private final long[] offsets = new long[VOLATILE.length];
		/** Registers each instruction reads (upper 32 bits) and writes (lower 32 bits) */
		private final Map<Address, Long> access = new HashMap<>();
		private final Map<Function, Integer> changes = new HashMap<>();
		private final Map<Function, Integer> inputs = new HashMap<>();
		private final Map<Function, Set<Function>> relying = new HashMap<>();
		private List<Call> calls;

		RegisterUse(Program program, TaskMonitor monitor) throws CancelledException {
			this.listing = program.getListing();
			this.functions = program.getFunctionManager();
			for (int i = 0; i < VOLATILE.length; i++) {
				offsets[i] = program.getRegister(VOLATILE[i]).getAddress().getOffset();
			}
			computeChanges(monitor);
		}

		private long access(Instruction instruction) {
			return access.computeIfAbsent(instruction.getAddress(), a -> {
				int reads = 0, writes = 0;
				for (PcodeOp op : instruction.getPcode()) {
					for (Varnode in : op.getInputs()) {
						reads |= mask(in) & ~writes; // not a value the instruction wrote first
					}
					writes |= mask(op.getOutput());
				}
				return ((long) reads << 32) | writes;
			});
		}

		private int mask(Varnode v) {
			if (v == null || !v.isRegister()) {
				return 0;
			}
			int m = 0;
			for (int i = 0; i < offsets.length; i++) {
				if (v.getOffset() < offsets[i] + 4 && offsets[i] < v.getOffset() + v.getSize()) {
					m |= 1 << i;
				}
			}
			return m;
		}

		private static int reads(long access) {
			return (int) (access >>> 32);
		}

		private static int writes(long access) {
			return (int) access;
		}

		/** The registers each function can change, through the functions it calls too. */
		private void computeChanges(TaskMonitor monitor) throws CancelledException {
			Map<Function, Set<Function>> callees = new HashMap<>();
			for (Function f : functions.getFunctions(true)) {
				monitor.checkCancelled();
				int w = 0;
				Set<Function> called = new HashSet<>();
				AddressSetView body = f.getBody();
				for (Instruction instruction : listing.getInstructions(body, true)) {
					w |= writes(access(instruction));
					FlowType flow = instruction.getFlowType();
					if (flow.isComputed() &&
						(flow.isCall() || instruction.getReferencesFrom().length == 0)) {
						w = ALL; // through a pointer, or an unresolved switch
					}
					for (Address target : instruction.getFlows()) {
						if (!flow.isCall() && body.contains(target)) {
							continue;
						}
						Function g = functions.getFunctionAt(target);
						if (g == null) {
							w = ALL; // into code of no function
						}
						else if (g != f) {
							called.add(g);
						}
					}
				}
				changes.put(f, w);
				callees.put(f, called);
			}
			boolean again = true;
			while (again) {
				monitor.checkCancelled();
				again = false;
				for (Map.Entry<Function, Integer> e : changes.entrySet()) {
					int w = e.getValue();
					for (Function g : callees.get(e.getKey())) {
						w |= changes.get(g);
					}
					if (w != e.getValue()) {
						e.setValue(w);
						again = true;
					}
				}
			}
		}

		int changes(Function f) {
			return f == null ? ALL : changes.getOrDefault(f, ALL);
		}

		/**
		 * The volatile registers a function does not change. Registers it reads before writing
		 * them count only if they hold parameters of its committed signature, as Decompiler
		 * Parameter ID commits them: the decompiler names any other input in an unaffected
		 * register {@code unaff_}, even a parameter.
		 */
		int kept(Function f) {
			int parameters = 0;
			if (f.getSignatureSource() != SourceType.DEFAULT) {
				for (Parameter p : f.getParameters()) {
					for (Varnode v : p.getVariableStorage().getVarnodes()) {
						parameters |= mask(v);
					}
				}
			}
			return ALL & ~changes(f) & ~(inputs(f) & ~parameters);
		}

		/** The callers that read registers the function keeps after calling it. */
		Set<Function> relyingCallers(Function f) {
			return relying.getOrDefault(f, Set.of());
		}

		/** The functions whose callers read registers they keep, and the registers each keeps. */
		Map<Function, Integer> reliedOn(TaskMonitor monitor) throws CancelledException {
			if (calls == null) {
				findCalls(monitor);
			}
			relying.clear();
			Map<Function, Integer> result = new HashMap<>();
			for (Call call : calls) {
				int kept = kept(call.callee);
				if ((kept & call.readsAfter) != 0) {
					result.put(call.callee, kept);
					relying.computeIfAbsent(call.callee, k -> new HashSet<>()).add(call.caller);
				}
			}
			return result;
		}

		/** A direct call, and the volatile registers the caller reads after it before writing. */
		private record Call(Function caller, Function callee, int readsAfter) {}

		/** The direct calls after which the caller reads volatile registers. */
		private void findCalls(TaskMonitor monitor) throws CancelledException {
			calls = new ArrayList<>();
			for (Function caller : functions.getFunctions(true)) {
				monitor.checkCancelled();
				for (Instruction instruction : listing.getInstructions(caller.getBody(), true)) {
					FlowType flow = instruction.getFlowType();
					Address next = instruction.getFallThrough();
					if (!flow.isCall() || flow.isComputed() || next == null) {
						continue;
					}
					int reads = -1;
					for (Address target : instruction.getFlows()) {
						Function callee = functions.getFunctionAt(target);
						if (callee == null || changes(callee) == ALL) {
							continue;
						}
						if (reads < 0) {
							reads = readsBeforeWriting(caller, next, ALL, MAX_STEPS);
						}
						if (reads != 0) {
							calls.add(new Call(caller, callee, reads));
						}
					}
				}
			}
		}

		/**
		 * Which of the registers {@code live} the function reads from {@code start} on before
		 * writing them, following at most {@code limit} instructions. A call reads the registers
		 * its callee reads before writing them, and writes the ones it changes. Returns are not
		 * reads of r3 and r4: before Decompiler Parameter ID it is not known whether a function
		 * returns a value, and most calls of functions that keep r3 would count.
		 */
		private int readsBeforeWriting(Function f, Address start, int live, int limit) {
			AddressSetView body = f.getBody();
			Map<Address, Integer> seen = new HashMap<>();
			Deque<Map.Entry<Address, Integer>> todo = new ArrayDeque<>();
			todo.push(Map.entry(start, live));
			int found = 0;
			int steps = 0;
			while (!todo.isEmpty() && steps++ < limit) {
				var item = todo.pop();
				Address a = item.getKey();
				int mask = item.getValue() & ~found & ~seen.getOrDefault(a, 0);
				if (mask == 0 || !body.contains(a)) {
					continue;
				}
				seen.merge(a, mask, (x, y) -> x | y);
				Instruction instruction = listing.getInstructionAt(a);
				if (instruction == null) {
					continue;
				}
				long acc = access(instruction);
				found |= reads(acc) & mask;
				mask &= ~writes(acc) & ~found;
				FlowType flow = instruction.getFlowType();
				if (flow.isCall()) {
					// an indirect call or a call of no function ends the search: what it reads
					// is not known
					for (Address target : instruction.getFlows()) {
						Function callee = functions.getFunctionAt(target);
						found |= inputs(callee) & mask;
						mask &= ~changes(callee);
					}
					if (flow.isComputed()) {
						mask = 0;
					}
				}
				else if (flow.isTerminal()) {
					continue;
				}
				else if (flow.isJump() || flow.isConditional()) {
					for (Address target : instruction.getFlows()) {
						if (body.contains(target)) {
							todo.push(Map.entry(target, mask));
						}
						else { // to another function, as a call
							found |= inputs(functions.getFunctionAt(target)) & mask;
						}
					}
				}
				Address next = instruction.getFallThrough();
				if (next != null && mask != 0) {
					todo.push(Map.entry(next, mask));
				}
			}
			return found;
		}

		/** The volatile registers a function reads before writing them; none if not known. */
		private int inputs(Function f) {
			if (f == null) {
				return 0;
			}
			Integer known = inputs.get(f);
			if (known != null) {
				return known;
			}
			inputs.put(f, ALL); // while computing it, for recursion
			// no limit: each instruction is visited at most once per register
			int in = readsBeforeWriting(f, f.getEntryPoint(), ALL, Integer.MAX_VALUE);
			inputs.put(f, in);
			return in;
		}
	}
}
