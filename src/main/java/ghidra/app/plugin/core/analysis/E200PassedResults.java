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
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.data.*;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.symbol.*;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

/**
 * Return types of functions whose callers use their result (part of {@link E200DataTypes}).
 * <p>
 * Decompiler Parameter ID finds a return value where a function sets r3 before returning, and
 * {@link E200TypeFlow} gives the functions it finds none in {@code void}. It misses two kinds
 * of results, which callers then show as {@code extraout_r3}:
 * <ul>
 * <li>Results passed on: e200 compilers do not turn {@code return g(x);} into a branch to
 * {@code g}. The function calls {@code g}, restores its frame and returns, and r3 holds what
 * {@code g} returned. Parameter ID sees that result only if the prototype of {@code g} had a
 * return value when the function was decompiled. Such wrappers are common, as in tables of
 * accessors that each call a shared routine.</li>
 * <li>Results that some paths compute and others get from an indirect call.</li>
 * </ul>
 * The result of a function is used where one of its callers reads r3 after calling it before
 * writing it, or returns it in turn from a function whose result is used. A store of several
 * registers, as startup code saves all of them with, is not a read, and a function whose
 * calling convention keeps r3 has no result. A function whose result is used and that returns
 * nothing so far gets the return type of the functions whose results it passes on, when every
 * one of its returns is reached from a direct call with no write to r3 in between and they all
 * have the same one. Otherwise, if an instruction of a caller reads the result (not only a
 * call, whose callee may ignore a parameter) and the function changes r3, it gets
 * {@code undefined4}, for the decompiler to show what it returns and later rounds to type
 * where they can. Functions whose return type the user set, or that return a value of a type
 * of their own, are left alone.
 */
final class E200PassedResults {

	/** Instructions followed after a call when looking for a read of r3 */
	private static final int MAX_STEPS = 256;

	private final Listing listing;
	private final FunctionManager functions;
	private final ReferenceManager references;
	private final Address r3;
	private final int r3Size;
	// What the code shows is kept between calls of apply: instructions, calls and calling
	// conventions do not change while types are inferred
	/** The functions whose results each function passes on, if it does on every return */
	private final Map<Function, Set<Function>> passedOn = new HashMap<>();
	/** How the callers of each function use its result */
	private final Map<Function, List<CallUse>> callUses = new HashMap<>();

	private record CallUse(Function caller, Use use) {}

	E200PassedResults(Program program) {
		this.listing = program.getListing();
		this.functions = program.getFunctionManager();
		this.references = program.getReferenceManager();
		Register r = program.getRegister("r3");
		this.r3 = r.getAddress();
		this.r3Size = r.getMinimumByteSize();
	}

	/**
	 * Gives the functions whose results their callers use, and that return nothing so far, a
	 * return type; returns the functions typed.
	 */
	List<Function> apply(TaskMonitor monitor) throws CancelledException {
		Set<Function> candidates = new HashSet<>();
		for (Function f : functions.getFunctions(true)) {
			monitor.checkCancelled();
			if (open(f)) {
				candidates.add(f);
			}
		}
		Map<Function, Use> used = usedResults(candidates, monitor);
		Set<Function> typed = new LinkedHashSet<>();
		boolean again = true;
		while (again) { // a wrapper of a wrapper is typed once the inner one is
			monitor.checkCancelled();
			again = false;
			for (Function f : used.keySet()) {
				DataType type = passedType(f);
				if (type != null && setReturnType(f, type)) {
					typed.add(f);
					again = true;
				}
			}
		}
		for (Map.Entry<Function, Use> e : used.entrySet()) {
			Function f = e.getKey();
			if (e.getValue() == Use.READ && open(f) && changesR3(f) &&
				setReturnType(f, Undefined4DataType.dataType)) {
				typed.add(f);
			}
		}
		return new ArrayList<>(typed);
	}

	/**
	 * Whether a function returns nothing so far, its signature is the analysis' to set, and it
	 * does not keep r3 (a caller reading r3 then reads its own value)
	 */
	private static boolean open(Function f) {
		DataType type = f.getReturnType();
		return !f.isThunk() && !f.getSignatureSource().isHigherPriorityThan(SourceType.ANALYSIS) &&
			(type == null || type instanceof VoidDataType || type instanceof DefaultDataType) &&
			!keepsR3(f);
	}

	/** Whether a function may change r3: an instruction writes it, or it calls a function */
	private boolean changesR3(Function f) {
		for (Instruction instruction : listing.getInstructions(f.getBody(), true)) {
			if (instruction.getFlowType().isCall() || writesR3(instruction)) {
				return true;
			}
		}
		return false;
	}

	/** The return type of the functions whose results {@code f} passes on, if all agree. */
	private DataType passedType(Function f) {
		DataType type = null;
		if (!passedOn.containsKey(f)) {
			passedOn.put(f, passedCallees(f));
		}
		Set<Function> callees = passedOn.get(f);
		if (callees == null) {
			return null;
		}
		for (Function g : callees) {
			DataType t = resolve(g).getReturnType();
			if (t == null || !returnsValue(t) || type != null && !type.isEquivalent(t)) {
				return null;
			}
			type = t;
		}
		return type;
	}

	private static boolean returnsValue(DataType type) {
		return !(type instanceof VoidDataType) && !(type instanceof DefaultDataType) &&
			type.getLength() > 0;
	}

	/** Sets the return type if it is not known or void; returns whether it changed. */
	private static boolean setReturnType(Function f, DataType type) {
		DataType current = f.getReturnType();
		if (f.isThunk() || f.getSignatureSource().isHigherPriorityThan(SourceType.ANALYSIS) ||
			current != null && returnsValue(current) && !Undefined.isUndefined(current) ||
			current != null && current.isEquivalent(type)) {
			return false;
		}
		if (current != null && Undefined.isUndefined(current) &&
			!(current instanceof DefaultDataType) && current.getLength() != type.getLength()) {
			return false; // an undefined4 is not a ushort
		}
		try {
			f.setReturnType(type, SourceType.ANALYSIS);
			return true;
		}
		catch (InvalidInputException e) {
			Msg.warn(E200Analyzer.class, "Could not set the return type of " + f + ": " + e);
			return false;
		}
	}

	private static Function resolve(Function f) {
		return f.isThunk() ? f.getThunkedFunction(true) : f;
	}

	/**
	 * The functions that {@code f} returns the results of, when every return of {@code f} is
	 * reached from a direct call with no write to r3 in between; otherwise null.
	 */
	private Set<Function> passedCallees(Function f) {
		AddressSetView body = f.getBody();
		Set<Function> callees = new HashSet<>();
		Deque<Instruction> todo = new ArrayDeque<>();
		Set<Address> seen = new HashSet<>();
		boolean returns = false;
		for (Instruction instruction : listing.getInstructions(body, true)) {
			FlowType flow = instruction.getFlowType();
			if (flow.isTerminal() && !flow.isCall()) {
				if (flow.isComputed() || writesR3(instruction)) {
					return null;
				}
				List<Instruction> before = predecessors(instruction, body);
				if (before == null || instruction.getAddress().equals(f.getEntryPoint())) {
					return null;
				}
				returns = true;
				todo.addAll(before);
			}
		}
		while (!todo.isEmpty()) {
			Instruction instruction = todo.pop();
			if (!seen.add(instruction.getAddress())) {
				continue;
			}
			FlowType flow = instruction.getFlowType();
			if (flow.isCall()) {
				Function callee = directCallee(instruction);
				if (callee == null || callee.equals(f)) {
					return null;
				}
				callees.add(callee);
				continue;
			}
			if (writesR3(instruction) || instruction.getAddress().equals(f.getEntryPoint())) {
				return null; // r3 set here, or the parameter in r3 returned
			}
			List<Instruction> before = predecessors(instruction, body);
			if (before == null || before.isEmpty()) {
				return null;
			}
			todo.addAll(before);
			if (seen.size() > MAX_STEPS) {
				return null;
			}
		}
		return returns && !callees.isEmpty() ? callees : null;
	}

	/**
	 * The instructions control reaches {@code instruction} from in {@code body}: the one before
	 * it if it falls through, and those that jump to it; null if one is outside the body.
	 */
	private List<Instruction> predecessors(Instruction instruction, AddressSetView body) {
		List<Instruction> list = new ArrayList<>();
		Instruction previous = listing.getInstructionBefore(instruction.getAddress());
		if (previous != null && instruction.getAddress().equals(previous.getFallThrough()) &&
			!previous.getFlowType().isTerminal()) {
			list.add(previous);
		}
		for (Reference ref : references.getReferencesTo(instruction.getAddress())) {
			if (!ref.getReferenceType().isFlow() || ref.getReferenceType().isCall()) {
				continue;
			}
			if (!body.contains(ref.getFromAddress())) {
				return null;
			}
			Instruction from = listing.getInstructionAt(ref.getFromAddress());
			if (from != null) {
				list.add(from);
			}
		}
		return list;
	}

	private Function directCallee(Instruction instruction) {
		if (instruction.getFlowType().isComputed()) {
			return null;
		}
		Address[] flows = instruction.getFlows();
		if (flows.length != 1) {
			return null;
		}
		return functions.getFunctionAt(flows[0]);
	}

	/**
	 * The functions whose results a caller uses, and how: it reads r3 after calling them before
	 * writing it, or returns it from a function whose result is used in turn.
	 */
	private Map<Function, Use> usedResults(Set<Function> candidates, TaskMonitor monitor)
			throws CancelledException {
		Map<Function, Use> used = new HashMap<>();
		Map<Function, Set<Function>> passedBy = new HashMap<>(); // callee -> callers passing it on
		// the callers that pass a result on are followed in turn, typed or not
		Deque<Function> todo = new ArrayDeque<>(candidates);
		Set<Function> visited = new HashSet<>(candidates);
		while (!todo.isEmpty()) {
			Function f = todo.pop();
			for (CallUse c : callUses(f, monitor)) {
				switch (c.use()) {
					case READ, ARGUMENT -> used.merge(f, c.use(), Use::stronger);
					case RETURNED -> {
						passedBy.computeIfAbsent(f, k -> new HashSet<>()).add(c.caller());
						if (visited.add(c.caller())) {
							todo.push(c.caller());
						}
					}
					case NONE -> {
					}
				}
			}
		}
		// a function passed on by a caller whose result is used, as the caller's is
		boolean again = true;
		while (again) {
			again = false;
			for (Map.Entry<Function, Set<Function>> e : passedBy.entrySet()) {
				for (Function caller : e.getValue()) {
					Use use = used.get(caller);
					if (use != null &&
						used.get(e.getKey()) != used.merge(e.getKey(), use, Use::stronger)) {
						again = true; // stronger than before, or new
					}
				}
			}
		}
		return used;
	}

	/** How each call of {@code f} uses its result */
	private List<CallUse> callUses(Function f, TaskMonitor monitor) throws CancelledException {
		List<CallUse> list = callUses.get(f);
		if (list != null) {
			return list;
		}
		list = new ArrayList<>();
		for (Reference ref : references.getReferencesTo(f.getEntryPoint())) {
			monitor.checkCancelled();
			if (!ref.getReferenceType().isCall()) {
				continue;
			}
			Instruction call = listing.getInstructionAt(ref.getFromAddress());
			Function caller = functions.getFunctionContaining(ref.getFromAddress());
			if (call == null || caller == null || call.getFallThrough() == null) {
				continue;
			}
			Use use = useAfter(caller, call.getFallThrough());
			if (use != Use.NONE) {
				list.add(new CallUse(caller, use));
			}
		}
		callUses.put(f, list);
		return list;
	}

	private enum Use {
		/** An instruction reads r3 */
		READ,
		/** A call reads r3, as a parameter its callee may ignore */
		ARGUMENT,
		RETURNED, NONE;

		static Use stronger(Use a, Use b) {
			return a.ordinal() <= b.ordinal() ? a : b;
		}
	}

	/**
	 * How the caller uses r3 from {@code start} on: reads it before writing it, passes it to a
	 * call, returns it, or none of these, following at most {@link #MAX_STEPS} instructions. A
	 * call reads r3 when the callee has a parameter in it, and keeps it when its calling
	 * convention says so.
	 */
	private Use useAfter(Function caller, Address start) {
		AddressSetView body = caller.getBody();
		Deque<Address> todo = new ArrayDeque<>();
		Set<Address> seen = new HashSet<>();
		todo.push(start);
		boolean returned = false;
		boolean argument = false;
		int steps = 0;
		while (!todo.isEmpty() && steps++ < MAX_STEPS) {
			Address a = todo.pop();
			if (!body.contains(a) || !seen.add(a)) {
				continue;
			}
			Instruction instruction = listing.getInstructionAt(a);
			if (instruction == null) {
				continue;
			}
			FlowType flow = instruction.getFlowType();
			if (flow.isCall()) {
				Function callee = directCallee(instruction);
				if (callee == null) {
					continue;
				}
				callee = resolve(callee);
				if (hasParameterInR3(callee)) {
					argument = true;
					continue;
				}
				if (!keepsR3(callee)) {
					continue;
				}
			}
			else if (readsR3(instruction) && !storesMultiple(instruction)) {
				return Use.READ;
			}
			else if (flow.isTerminal()) {
				returned |= !flow.isComputed();
				continue;
			}
			if (!flow.isCall() && writesR3(instruction)) {
				continue;
			}
			if (flow.isJump() || flow.isConditional()) {
				for (Address target : instruction.getFlows()) {
					todo.push(target);
				}
			}
			Address next = instruction.getFallThrough();
			if (next != null) {
				todo.push(next);
			}
		}
		return argument ? Use.ARGUMENT : returned ? Use.RETURNED : Use.NONE;
	}

	private boolean hasParameterInR3(Function f) {
		for (Parameter p : f.getParameters()) {
			for (Varnode v : p.getVariableStorage().getVarnodes()) {
				if (overlapsR3(v)) {
					return true;
				}
			}
		}
		return false;
	}

	private static boolean keepsR3(Function f) {
		String convention = f.getCallingConventionName();
		if (convention == null || !convention.startsWith(E200KeptRegisters.PREFIX)) {
			return false;
		}
		// __keeps_r3to6_r8to12, __keeps_r0_r3_r4, ...: a run or a register naming r3
		for (String part : convention.substring(E200KeptRegisters.PREFIX.length()).split("_")) {
			if (!part.matches("r\\d+(to\\d+)?")) {
				continue;
			}
			String[] range = part.substring(1).split("to");
			int lo = Integer.parseInt(range[0]);
			int hi = range.length > 1 ? Integer.parseInt(range[1]) : lo;
			if (lo <= 3 && 3 <= hi) {
				return true;
			}
		}
		return false;
	}

	/**
	 * A store of several registers, as startup code saves all of them with: r3 among the rest
	 * is not a read of a result
	 */
	private static boolean storesMultiple(Instruction instruction) {
		return instruction.getMnemonicString().contains("stm");
	}

	private boolean readsR3(Instruction instruction) {
		boolean written = false;
		for (PcodeOp op : instruction.getPcode()) {
			for (Varnode in : op.getInputs()) {
				if (!written && overlapsR3(in)) {
					return true;
				}
			}
			written |= overlapsR3(op.getOutput());
		}
		return false;
	}

	private boolean writesR3(Instruction instruction) {
		for (PcodeOp op : instruction.getPcode()) {
			if (overlapsR3(op.getOutput())) {
				return true;
			}
		}
		return false;
	}

	private boolean overlapsR3(Varnode v) {
		return v != null && v.isRegister() && v.getOffset() < r3.getOffset() + r3Size &&
			r3.getOffset() < v.getOffset() + v.getSize();
	}
}
