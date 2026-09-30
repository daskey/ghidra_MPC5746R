"""Checks the p-code of VLE instructions against vle_model.py; see README.md.

  python vle_tests.py check results.tsv [--show N]

results.tsv comes from RunVleTests.java. Every register, CR field, XER bit, LR, CTR, the
next PC and the stored bytes are compared; the model skips encodings whose result the
architecture leaves undefined. Exits with status 1 if any result differs.
"""
import collections
import csv
import sys

import vle_model as model

GPRS = [f'r{i}' for i in range(32)]
CRS = [f'cr{i}' for i in range(8)]
OTHER = ['xer_so', 'xer_ov', 'xer_ca', 'LR', 'CTR']
STATE = GPRS + CRS + OTHER


def expected_and_actual(row, image):
    initial = [int(row[k], 16) for k in STATE]
    actual = [int(row['out_' + k], 16) for k in STATE]
    address = int(row['address'], 16)
    code = bytes.fromhex(row['bytes'])
    st = model.State(initial, address, image)
    result = model.execute(row['mnemonic'], row['operands'], st, len(code))
    expected = list(initial)
    masks = [None] * len(STATE)
    for n, v in result.gpr.items():
        expected[n] = v & model.M32
    for n, v in result.cr.items():
        if isinstance(v, tuple):  # only the GT bit is defined
            masks[32 + n] = model.GT
            v = v[1]
        expected[32 + n] = v
    for name, v in result.xer.items():
        expected[STATE.index('xer_' + name)] = v
    if result.lr is not None:
        expected[STATE.index('LR')] = result.lr & model.M32
    if result.ctr is not None:
        expected[STATE.index('CTR')] = result.ctr & model.M32
    differences = []
    for i, name in enumerate(STATE):
        e, a = expected[i], actual[i]
        if masks[i] is not None:
            e, a = e & masks[i], a & masks[i]
        if e != a:
            differences.append(f'{name}: expected {e:x} got {a:x} (was {initial[i]:x})')
    pc = int(row['out_pc'], 16)
    if pc != result.pc:
        differences.append(f'pc: expected {result.pc:x} got {pc:x}')
    memory = {}
    if row['memory'] != '-':
        for item in row['memory'].split(','):
            a, b = item.split('=')
            memory[int(a, 16)] = int(b, 16)
    if memory != result.memory:
        differences.append(f'memory: expected {fmt(result.memory)} got {fmt(memory)}')
    return differences


class TestImage(dict):
    """The imported test image: zeros with each tested encoding at its address. Reads
    outside it return the pattern (see RunVleTests.java)."""

    def __init__(self, rows, base=0x10000000, size=0x40000):
        super().__init__()
        self.base, self.size = base, size
        for row in rows:
            address = int(row['address'], 16)
            for i, b in enumerate(bytes.fromhex(row['bytes'])):
                self[address + i] = b

    def get(self, address, default):
        if self.base <= address < self.base + self.size:
            return super().get(address, 0)
        return default


def fmt(memory):
    return ','.join(f'{a:x}={b:02x}' for a, b in sorted(memory.items())) or '-'


def main():
    if len(sys.argv) < 3 or sys.argv[1] != 'check':
        print(__doc__)
        sys.exit(2)
    show = int(sys.argv[sys.argv.index('--show') + 1]) if '--show' in sys.argv else 3
    counts = collections.Counter()
    failures = collections.defaultdict(list)
    skipped = collections.Counter()
    with open(sys.argv[2]) as stream:
        rows = list(csv.DictReader(stream, delimiter='\t'))
    image = TestImage(rows)
    for row in rows:
        mnemonic = row['mnemonic']
        try:
            differences = expected_and_actual(row, image)
        except model.Skip as reason:
            skipped[f'{mnemonic}: {reason}'] += 1  # also covers emulator faults there
            continue
        if row['status'] != 'ok':
            differences = [row['status']]
        counts[mnemonic] += 1
        if differences:
            failures[mnemonic].append((row, differences))
    tested = sum(counts.values())
    failed = sum(len(v) for v in failures.values())
    print(f'{tested} results checked for {len(counts)} mnemonics, {failed} differ, '
          f'{sum(skipped.values())} skipped')
    for reason, n in sorted(skipped.items()):
        print(f'  skipped {n:5d}  {reason}')
    for mnemonic, items in sorted(failures.items()):
        print(f'\n{mnemonic}: {len(items)} of {counts[mnemonic] + len(items)} differ')
        for row, differences in items[:show]:
            print(f"  {row['address']} {row['bytes']} {mnemonic} {row['operands'].replace('|', ',')}")
            for d in differences:
                print(f'      {d}')
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
