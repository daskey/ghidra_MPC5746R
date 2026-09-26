# LSP semantics tests

Runs every LSP instruction in Ghidra's p-code emulator and compares the results with
`lsp_model.py`, an independent Python model written directly from the pseudo-RTL of the
NXP *Lightweight Signal Processing APU Reference Manual* (Rev. 3, section 1.6).

`lsp_tests.py gen` builds a raw test image with random register values, biased toward
saturation edge cases. It uses rD=r4 (pair r4:r5), rA=r6, rB=r7 and a data region at
0x100000 for the loads and stores. `RunLspTests.java` steps each test instruction once and
records the registers, the CR fields, SPEFSCR and any memory writes.

Run the steps in a scratch directory; the test files are written to the current directory:

```
python <repo>/tools/lsp_test/lsp_tests.py gen 250

<ghidra>/support/analyzeHeadless <project dir> LspTest -import lsp_tests.bin \
    -loader BinaryLoader -loader-baseAddr 0 -processor PowerPC:BE:32:VLE-e200 -noanalysis \
    -scriptPath <repo>/tools/lsp_test \
    -postScript RunLspTests.java lsp_tests.tsv lsp_results.tsv 100000 102000 -deleteProject

python <repo>/tools/lsp_test/lsp_tests.py check
```

The language must be the one built from this checkout, so install the extension first.
The last argument of `gen` is the number of tests per instruction (half as many, at least
20, for loads and stores).
