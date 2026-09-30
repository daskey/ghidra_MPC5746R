// Runs VLE instructions with random register states in the p-code emulator for
// tools/vle_test/vle_tests.py, which checks the results against an independent model.
//
// Encodings are random 16- and 32-bit words that Ghidra decodes as one of the mnemonics in
// the list (the decoding itself is checked against GNU objdump, see the module README). Each is run
// once per state from a fresh set of registers. Reads of memory outside the test code return
// a pattern that the model reproduces; stores are recorded and then undone.
//
// Args: <mnemonics.txt> <results.tsv> <seed> <encodings per mnemonic> <states per encoding>
//       <random words to try>
//@category Test
import java.io.*;
import java.math.BigInteger;
import java.nio.file.*;
import java.util.*;

import ghidra.app.emulator.EmulatorHelper;
import ghidra.app.script.GhidraScript;
import ghidra.app.util.PseudoDisassembler;
import ghidra.app.util.PseudoInstruction;
import ghidra.pcode.memstate.MemoryFaultHandler;
import ghidra.program.model.address.Address;

public class RunVleTests extends GhidraScript {

	static final String[] STATE = stateNames();

	static String[] stateNames() {
		List<String> names = new ArrayList<>();
		for (int i = 0; i < 32; i++) {
			names.add("r" + i);
		}
		for (int i = 0; i < 8; i++) {
			names.add("cr" + i);
		}
		names.addAll(List.of("xer_so", "xer_ov", "xer_ca", "LR", "CTR"));
		return names.toArray(new String[0]);
	}

	/** Contents of memory the test code does not occupy; vle_model.pattern must agree. */
	static byte pattern(long address) {
		int h = (int) address * 0x9E3779B1;
		return (byte) (h >>> 24);
	}

	@Override
	protected void run() throws Exception {
		String[] args = getScriptArgs();
		Set<String> wanted = new TreeSet<>();
		for (String line : Files.readAllLines(Path.of(args[0]))) {
			if (!line.isBlank() && !line.startsWith("#")) {
				wanted.add(line.trim());
			}
		}
		Random rng = new Random(Long.parseLong(args[2]));
		int perMnemonic = Integer.parseInt(args[3]);
		int states = Integer.parseInt(args[4]);
		long attempts = Long.parseLong(args[5]);

		// Collect encodings: decode random words at an aligned address.
		Address codeBase = currentProgram.getMinAddress();
		PseudoDisassembler pd = new PseudoDisassembler(currentProgram);
		Map<String, List<byte[]>> encodings = new TreeMap<>();
		Set<String> seen = new HashSet<>();
		byte[] word = new byte[4];
		for (long i = 0; i < attempts; i++) {
			if ((i & 0xffff) == 0) {
				monitor.checkCancelled();
			}
			rng.nextBytes(word);
			// X-form (opcode 31) and EFPU2 (opcode 4) instructions are a small share of
			// random words; give them more tries
			int major = rng.nextInt(4);
			if (major < 2) {
				word[0] = (byte) ((major == 0 ? 31 : 4) << 2 | (word[0] & 3));
				if (rng.nextInt(4) == 0) {
					// operand fields zero, as in single-operand forms (mfcr, efsabs, ...)
					word[1] &= (byte) 0xe0;
					word[2] &= 0x07;
				}
			}
			PseudoInstruction instruction;
			try {
				instruction = pd.disassemble(codeBase, word);
			}
			catch (Exception e) {
				continue;
			}
			if (instruction == null) {
				continue;
			}
			String mnemonic = instruction.getMnemonicString();
			List<byte[]> list = encodings.computeIfAbsent(mnemonic, m -> new ArrayList<>());
			if (!wanted.contains(mnemonic) || list.size() >= perMnemonic) {
				continue;
			}
			byte[] bytes = Arrays.copyOf(word, instruction.getLength());
			if (seen.add(HexFormat.of().formatHex(bytes))) {
				list.add(bytes);
			}
		}
		for (String m : wanted) {
			if (encodings.getOrDefault(m, List.of()).isEmpty()) {
				println("No encoding found for " + m);
			}
		}

		// Lay the encodings out 8 bytes apart and run them.
		List<byte[]> all = new ArrayList<>();
		encodings.forEach((m, list) -> {
			if (wanted.contains(m)) {
				all.addAll(list);
			}
		});
		long size = currentProgram.getMemory().getSize();
		if (all.size() * 8L > size) {
			throw new IllegalArgumentException("Test image too small for " + all.size() + " encodings");
		}
		EmulatorHelper emu = newEmulator();
		PseudoDisassembler check = new PseudoDisassembler(currentProgram);
		int id = 0;
		try (BufferedWriter out = new BufferedWriter(new FileWriter(args[1]), 1 << 20)) {
			out.write("id\taddress\tbytes\tmnemonic\toperands\tstatus\t" + String.join("\t", STATE) + "\t" +
				String.join("\t", Arrays.stream(STATE).map(s -> "out_" + s).toList()) +
				"\tout_pc\tmemory\n");
			for (int n = 0; n < all.size(); n++) {
				Address address = codeBase.add(8L * n);
				emu.writeMemory(address, all.get(n));
				PseudoInstruction instruction = check.disassemble(address, Arrays.copyOf(all.get(n), 4));
				StringBuilder operands = new StringBuilder();
				for (int i = 0; i < instruction.getNumOperands(); i++) {
					if (i > 0) {
						operands.append('|');
					}
					operands.append(instruction.getDefaultOperandRepresentation(i));
				}
				String mnemonic = instruction.getMnemonicString();
				for (int s = 0; s < states; s++) {
					monitor.checkCancelled();
					long[] initial = randomState(rng, mnemonic);
					for (int i = 0; i < STATE.length; i++) {
						emu.writeRegister(STATE[i], BigInteger.valueOf(initial[i]));
					}
					emu.writeRegister(emu.getPCRegister(), BigInteger.valueOf(address.getOffset()));
					emu.enableMemoryWriteTracking(true);
					String status = "ok";
					try {
						if (!emu.step(monitor)) {
							status = "fault:" + emu.getLastError();
						}
					}
					catch (Exception e) {
						status = "exception:" + e.getMessage();
					}
					StringBuilder line = new StringBuilder();
					line.append(id++).append('\t').append(address).append('\t')
							.append(HexFormat.of().formatHex(all.get(n))).append('\t')
							.append(mnemonic).append('\t').append(operands).append('\t')
							.append(status.replace('\t', ' ').replace('\n', ' '));
					for (long v : initial) {
						line.append('\t').append(Long.toHexString(v));
					}
					for (String r : STATE) {
						line.append('\t').append(emu.readRegister(r).toString(16));
					}
					line.append('\t').append(emu.readRegister(emu.getPCRegister()).toString(16));
					StringBuilder memory = new StringBuilder();
					for (var range : emu.getTrackedMemoryWriteSet()) {
						if (!range.getMinAddress().isMemoryAddress()) {
							continue; // p-code temporaries
						}
						for (long o = range.getMinAddress().getOffset(); o <= range.getMaxAddress().getOffset(); o++) {
							Address a = range.getMinAddress().getNewAddress(o);
							if (memory.length() > 0) {
								memory.append(',');
							}
							memory.append(Long.toHexString(a.getOffset())).append('=')
									.append(String.format("%02x", emu.readMemoryByte(a)));
							emu.writeMemory(a, new byte[] { pattern(a.getOffset()) });
						}
					}
					emu.enableMemoryWriteTracking(false);
					line.append('\t').append(memory.length() > 0 ? memory : "-");
					out.write(line.append('\n').toString());
					if (!status.equals("ok")) {
						// a fault stops the emulator for good; start over for the next state
						emu.dispose();
						emu = newEmulator();
						emu.writeMemory(address, all.get(n));
					}
				}
			}
		}
		emu.dispose();
		println("Ran " + id + " tests of " + all.size() + " encodings");
	}

	private EmulatorHelper newEmulator() {
		EmulatorHelper emu = new EmulatorHelper(currentProgram);
		emu.setMemoryFaultHandler(new MemoryFaultHandler() {
			@Override
			public boolean uninitializedRead(Address address, int length, byte[] buf, int offset) {
				for (int i = 0; i < length; i++) {
					buf[offset + i] = pattern(address.getOffset() + i);
				}
				return true;
			}

			@Override
			public boolean unknownAddress(Address address, boolean write) {
				return false;
			}
		});
		return emu;
	}

	private static final long[] EDGE = { 0, 1, 2, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, 0x10000,
		0x7fffffffL, 0x80000000L, 0x80000001L, 0xfffffffeL, 0xffffffffL, 0x1f, 0x20, 0x21 };

	/** r0-r31, cr0-cr7, xer_so, xer_ov, xer_ca, LR, CTR */
	private static long[] randomState(Random rng, String mnemonic) {
		long[] s = new long[STATE.length];
		boolean floats = mnemonic.startsWith("efs");
		for (int i = 0; i < 32; i++) {
			double k = rng.nextDouble();
			if (floats) {
				// normal single-precision values of varied magnitude and sign
				float f = (float) ((rng.nextDouble() * 2 - 1) * Math.pow(10, rng.nextInt(13) - 6));
				s[i] = k < 0.1 ? EDGE[rng.nextInt(EDGE.length)] & 0x7fffffffL
						: Float.floatToRawIntBits(f) & 0xffffffffL;
			}
			else if (k < 0.3) {
				s[i] = EDGE[rng.nextInt(EDGE.length)];
			}
			else if (k < 0.5) {
				s[i] = rng.nextInt(64); // shift counts, small indexes
			}
			else if (k < 0.7) {
				s[i] = (rng.nextInt(0x10000) - 0x8000) & 0xffffffffL;
			}
			else {
				s[i] = rng.nextInt() & 0xffffffffL;
			}
		}
		for (int i = 0; i < 8; i++) {
			s[32 + i] = rng.nextInt(16);
		}
		s[40] = rng.nextInt(2);
		s[41] = rng.nextInt(2);
		s[42] = rng.nextInt(2);
		s[43] = (rng.nextInt() & 0xfffffffeL);
		s[44] = rng.nextInt(4) == 0 ? rng.nextInt(3) : rng.nextInt() & 0xffffffffL; // CTR near 1
		return s;
	}
}
