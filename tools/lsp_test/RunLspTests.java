// Executes single instructions in the p-code emulator for tools/lsp_test/lsp_tests.py.
// Input lines:  addr r0..r7 cr0..cr7 spefscr   (hex, tab separated)
// Output lines: addr status r0..r9 cr0..cr7 spefscr memdiff
//   memdiff: comma separated addr=byte for bytes of [memLo, memHi) that changed
// Args: <tests.tsv> <results.tsv> <memLo> <memHi>
//@category Test
import java.io.*;
import java.math.BigInteger;

import ghidra.app.emulator.EmulatorHelper;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.lang.Register;

public class RunLspTests extends GhidraScript {
	@Override
	protected void run() throws Exception {
		String[] args = getScriptArgs();
		long memLo = Long.parseLong(args[2], 16);
		long memHi = Long.parseLong(args[3], 16);
		int memLen = (int) (memHi - memLo);
		Address memStart = toAddr(memLo);
		byte[] original = new byte[memLen];
		currentProgram.getMemory().getBytes(memStart, original);

		EmulatorHelper emu = new EmulatorHelper(currentProgram);
		Register spefscr = currentProgram.getRegister("SPEFSCR");
		if (spefscr == null) {
			spefscr = currentProgram.getRegister("spr200");
		}
		println("SPEFSCR register: " + spefscr);
		String[] gpr = new String[10];
		for (int i = 0; i < gpr.length; i++) {
			gpr[i] = "r" + i;
		}
		int count = 0, errors = 0;
		try (BufferedReader in = new BufferedReader(new FileReader(args[0]));
				BufferedWriter out = new BufferedWriter(new FileWriter(args[1]), 1 << 20)) {
			String line;
			while ((line = in.readLine()) != null) {
				if ((count++ & 0xfff) == 0) {
					monitor.checkCancelled();
				}
				String[] f = line.split("\t");
				long addr = Long.parseLong(f[0], 16);
				for (int i = 0; i < 8; i++) {
					emu.writeRegister(gpr[i], new BigInteger(f[1 + i], 16));
				}
				emu.writeRegister(gpr[8], BigInteger.valueOf(0x88888888L));
				emu.writeRegister(gpr[9], BigInteger.valueOf(0x99999999L));
				for (int i = 0; i < 8; i++) {
					emu.writeRegister("cr" + i, new BigInteger(f[9 + i], 16));
				}
				emu.writeRegister(spefscr, new BigInteger(f[17], 16));
				emu.writeRegister(emu.getPCRegister(), BigInteger.valueOf(addr));
				String status = "ok";
				try {
					if (!emu.step(monitor)) {
						status = "fault:" + emu.getLastError();
						errors++;
					}
				}
				catch (Exception e) {
					status = "exception:" + e.getMessage();
					errors++;
				}
				StringBuilder sb = new StringBuilder();
				sb.append(f[0]).append('\t').append(status.replace('\t', ' ').replace('\n', ' '));
				for (String r : gpr) {
					sb.append('\t').append(emu.readRegister(r).toString(16));
				}
				for (int i = 0; i < 8; i++) {
					sb.append('\t').append(emu.readRegister("cr" + i).toString(16));
				}
				sb.append('\t').append(emu.readRegister(spefscr).toString(16));
				byte[] now = emu.readMemory(memStart, memLen);
				StringBuilder diff = new StringBuilder();
				for (int i = 0; i < memLen; i++) {
					if (now[i] != original[i]) {
						if (diff.length() > 0) {
							diff.append(',');
						}
						diff.append(Long.toHexString(memLo + i)).append('=')
								.append(Integer.toHexString(now[i] & 0xff));
					}
				}
				if (diff.length() > 0) {
					emu.writeMemory(memStart, original.clone()); // full pages are not copied
				}
				sb.append('\t').append(diff);
				out.write(sb.toString());
				out.write('\n');
			}
		}
		emu.dispose();
		println("tests=" + count + " errors=" + errors);
	}
}
