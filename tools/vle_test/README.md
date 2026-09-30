# VLE semantics tests

Runs VLE instructions in Ghidra's p-code emulator from random register states and compares
every result with `vle_model.py`, an independent Python model written from the Power ISA
2.06 Book VLE and EREF 2.0 descriptions, not from the SLEIGH.

The instructions tested are listed in `mnemonics.txt`: those that the MPC5746R test
firmware uses, except the ones with opaque semantics (DCR, MPU, decorated storage,
MSR and interrupt control, barriers), plus every form of the conditional branch. That is
integer arithmetic, logic, shifts and rotates, compares, the CR and SPR moves the model
covers, loads and stores in all addressing forms, branches, the saturating e200z425
instructions and EFPU2.

`RunVleTests.java` decodes random instruction words (biased toward the X-form and EFPU2
opcodes, some with the operand fields cleared) and keeps up to N distinct encodings of each
mnemonic. Each encoding is stepped once from each of M random states: r0-r31, cr0-cr7, SO,
OV, CA, LR and CTR, with edge values (0, 1, 0x7fffffff, 0x80000000, 0xffffffff, shift
counts around 32, CTR near 1) and normal single-precision values for EFPU2. Memory outside
the test code reads a pattern of the address that the model reproduces; stores are recorded
and undone. `vle_tests.py check` then compares all registers, CR fields, XER bits, LR, CTR,
the next PC and the stored bytes.

Run the steps in a scratch directory with the extension installed from this checkout:

```
python -c "open('blank.bin', 'wb').write(bytes(0x40000))"

<ghidra>/support/analyzeHeadless <project dir> VleTest -import blank.bin \
    -loader BinaryLoader -loader-baseAddr 10000000 -processor PowerPC:BE:32:VLE-e200 -noanalysis \
    -scriptPath <repo>/tools/vle_test \
    -postScript RunVleTests.java <repo>/tools/vle_test/mnemonics.txt results.tsv 2 40 12 40000000 \
    -deleteProject

python <repo>/tools/vle_test/vle_tests.py check results.tsv
```

The arguments of `RunVleTests.java` are the mnemonic list, the output, the random seed,
the encodings per mnemonic, the states per encoding and the number of random words to try.
The image must start at 0x10000000 and be 256 KB, the layout `vle_tests.py` assumes.

## Results

With the arguments above: 7,556 encodings of 199 mnemonics, 90,672 runs. 88,647 results
agree with the model and none differ; 2,025 are skipped (below).

With Ghidra's own semantics for the instructions that `e200_isa.sinc` corrects, 5,259 of
88,150 results of the 198 instructions tested then differ (`e_addwss` does not decode
there), all in these instructions of
Ghidra's `ppc_vle.sinc`:

| Instructions | Results that differ | Ghidra's semantics | Correct |
|---|---|---|---|
| `e_b<cc>l`, `e_bdnzl`, `e_bdzl` (conditional branch and link) | 4,800 of 9,600 | sets LR only when taken, and calls the address stored in the word at the target | sets LR either way and calls the target |
| `e_rlwinm`, `e_rlwimi` | 221 of 1,181 | with MB > ME, a mask without bits MB and ME | bits MB to 31 and 0 to ME |
| `se_srw`, `se_sraw` | 231 of 1,191 | shift by the low 5 bits of rY | the low 6 bits: 32 to 63 shift all bits out |
| `se_sraw`, `se_srawi` | 7 of 487 for `se_srawi` | CA set for a negative value and any nonzero shift | CA set when 1 bits are shifted out of a negative value |

## Skipped cases

The model raises `Skip` where the architecture leaves the result undefined or where the
module's p-code deliberately differs (see the modelling notes in the module README):

- divide by zero and 0x80000000 / -1 (`divw`, `divwu`)
- update forms with rA=0 or rA=rD, `e_lmw` with rA in the loaded range
- accesses that wrap past 0xFFFFFFFF, where the emulator stops with a fault
- EFPU2 operands or results that are not zero or normal numbers (denormals, infinities,
  NaNs), and NaN operands of `efsabs`/`efsneg`, whose payload the p-code float operations
  do not keep
- conversions of out-of-range values, which are not saturated
- `efsctui` of a value exactly halfway between two integers: the p-code rounds it up,
  the hardware to even
- `efsmax`/`efsmin` of equal values, which differ only in the sign of zero
- `se_bctr`/`se_bctrl` with an odd CTR, which the p-code does not round down
