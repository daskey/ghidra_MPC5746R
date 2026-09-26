"""Differential test of the LSP p-code against lsp_model.py; see README.md.

  python lsp_tests.py gen [per-insn]   -> lsp_tests.bin, lsp_tests.tsv, lsp_tests.meta
  (run RunLspTests.java in Ghidra on lsp_tests.bin -> lsp_results.tsv)
  python lsp_tests.py check           -> compare lsp_results.tsv with the model

Files are read and written in the current directory.
"""
import collections
import pathlib
import random
import sys

import lsp_model as model

TABLE = pathlib.Path(__file__).resolve().parent.parent / 'lsp_opcodes.txt'
DATA = 0x100000
DATA_LEN = 0x2000
IMAGE = DATA + DATA_LEN

EDGE16 = [0, 1, 2, 0x7fff, 0x8000, 0x8001, 0xffff, 0xfffe, 0x4000, 0xc000, 0x00ff, 0xff00]
EDGE32 = [0, 1, 0x7fffffff, 0x80000000, 0x80000001, 0xffffffff, 0x00008000, 0x7fff8000,
          0x7fff7fff, 0xffff8000, 0x007fff80, 0xff7fff80, 0x7fff0000, 0x80008000, 0x00010000]


def rnd32(rng):
    k = rng.random()
    if k < 0.25:
        return rng.choice(EDGE32)
    if k < 0.55:
        return (rng.choice(EDGE16) << 16) | rng.choice(EDGE16)
    if k < 0.7:
        return (rng.choice(EDGE16) << 16) | rng.getrandbits(16)
    if k < 0.8:
        # small signed values
        return rng.randint(-40000, 40000) & 0xffffffff
    return rng.getrandbits(32)


def load_table():
    rows = []
    for line in open(TABLE):
        if line.startswith('#') or not line.strip():
            continue
        name, xop, b16, ops, extra = line.rstrip('\n').split('\t')
        rows.append((name, int(xop, 16), None if b16 == '-' else int(b16), ops.split(','), extra))
    return rows


def ldst_form(name):
    m = model.LDST_RE.match(name)
    return (m.group(1), m.group(2) or '') if m else (None, None)


def make_case(rng, name, xop, b16, ops, extra):
    """Returns (word, regs[0..7], cr[8], spefscr)."""
    regs = [rnd32(rng) for _ in range(8)]
    cr = [rng.getrandbits(4) for _ in range(8)]
    spefscr = rng.getrandbits(32)
    rD, rA, rB = 4, 6, 7
    base, form = ldst_form(name)
    if base:
        store = base.startswith('zst')
        scale = model.LOAD_SCALE[base]
        if form in ('', 'u'):
            uimm = rng.randint(1 if form == 'u' else 0, 31)
            rB = uimm
            if form == '' and not store and rng.random() < 0.15:
                rA = 0
            else:
                regs[6] = DATA + rng.randrange(0, 0x1000, 2)
        elif form == 'x':
            if not store and rng.random() < 0.15:
                rA = 0
                regs[7] = DATA + rng.randrange(0, 0x1000, 2)
            else:
                regs[6] = DATA + rng.randrange(0, 0x1000, 2)
                regs[7] = rng.randrange(0, 0x800, 2)
        else:
            length = rng.randint(0, 63)
            last = (length << 3) | 7
            index = rng.choice([0, last, last - 1, rng.randint(0, last)])
            offset = rng.randint(-32, 31)
            regs[6] = 0x80000000 | ((offset & 0x3f) << 23) | (length << 13) | index
            if rng.random() < 0.2:
                regs[6] |= rng.getrandbits(2) << 29   # other modes: not modelled
            regs[7] = DATA + rng.randrange(0, 0x1000, 8)
    else:
        if ops[1:] == ['RA', 'EVUIMM'] or ops[1:] == ['RA', 'EVUIMM_LT16']:
            rB = rng.randint(0, 15 if ops[2] == 'EVUIMM_LT16' else 31)
        if ops == ['RD', 'SIMM']:
            rA = rng.randint(0, 31)
    word = (4 << 26)
    if ops[0] == 'CRFD':
        word |= (3 << 23) | (int(extra[3:], 2) << 21)
    else:
        word |= rD << 21
    word |= rA << 16
    if b16 is not None:
        word |= b16 << 11
    else:
        word |= rB << 11
    if ops[-1] == 'VX_OFF':
        word |= xop | rng.randint(1, 3)
    else:
        word |= xop
    return word, regs, cr, spefscr


def gen(per):
    rng = random.Random(0x1f5)
    image = bytearray(IMAGE)
    for k in range(DATA_LEN):
        image[DATA + k] = rng.getrandbits(8)
    lines, meta = [], []
    addr = 0
    for row in load_table():
        name = row[0]
        n = per if not ldst_form(name)[0] else max(per // 2, 20)
        for _ in range(n):
            word, regs, cr, spefscr = make_case(rng, *row)
            image[addr:addr + 4] = word.to_bytes(4, 'big')
            lines.append('\t'.join([f'{addr:x}'] + [f'{v:x}' for v in regs] +
                                   [f'{v:x}' for v in cr] + [f'{spefscr:x}']))
            meta.append(f'{addr:x}\t{name}\t{word:08x}')
            addr += 4
            if addr >= DATA:
                raise SystemExit('too many tests')
    open('lsp_tests.bin', 'wb').write(image)
    open('lsp_tests.tsv', 'w', newline='\n').write('\n'.join(lines) + '\n')
    open('lsp_tests.meta', 'w', newline='\n').write('\n'.join(meta) + '\n')
    print(f'{len(lines)} tests, image {len(image):#x} bytes')


def check(show=3):
    image = bytearray(open('lsp_tests.bin', 'rb').read())
    tests = {l.split('\t')[0]: l.rstrip('\n').split('\t') for l in open('lsp_tests.tsv')}
    meta = {l.split('\t')[0]: l.rstrip('\n').split('\t') for l in open('lsp_tests.meta')}
    results = [l.rstrip('\n').split('\t') for l in open('lsp_results.tsv')]
    bad = collections.defaultdict(list)
    ok = collections.Counter()
    for res in results:
        addr = res[0]
        t = tests[addr]
        _, name, word = meta[addr]
        word = int(word, 16)
        regs = [int(v, 16) for v in t[1:9]] + [0x88888888, 0x99999999]
        cr = [int(v, 16) for v in t[9:17]]
        st = model.State(regs + [0] * 22, cr, int(t[17], 16), image)
        model.execute(name, word, st)
        want_regs = st.r[:10]
        want = ([f'{v & 0xffffffff:x}' for v in want_regs] + [f'{v:x}' for v in st.cr] +
                [f'{st.spefscr & 0xffffffff:x}'])
        wmem = ','.join(f'{a:x}={b:x}' for a, b in sorted(st.written.items())
                        if image[a] != b)
        got = res[2:21]
        gmem = res[21] if len(res) > 21 else ''
        if res[1] != 'ok' or got != want or gmem != wmem:
            fields = ['r%d' % k for k in range(10)] + ['cr%d' % k for k in range(8)] + ['spefscr']
            diffs = [f'{f}: got {g} want {w}' for f, g, w in zip(fields, got, want) if g != w]
            if gmem != wmem:
                diffs.append(f'mem: got {gmem} want {wmem}')
            if res[1] != 'ok':
                diffs.insert(0, res[1])
            inputs = ' '.join(f'r{k}={v}' for k, v in zip(range(8), t[1:9]))
            bad[name].append(f'{word:08x} {inputs} cr={"".join(t[9:17])} spefscr={t[17]} :: ' +
                             '; '.join(diffs))
        else:
            ok[name] += 1
    names = sorted(set(m[1] for m in meta.values()))
    print(f'{len(results)} results, {sum(ok.values())} ok, '
          f'{sum(len(v) for v in bad.values())} mismatches in {len(bad)} instructions')
    for name in names:
        if name in bad:
            print(f'{name}: {len(bad[name])} bad, {ok[name]} ok')
            for line in bad[name][:show]:
                print('    ' + line)


if __name__ == '__main__':
    if sys.argv[1] == 'gen':
        gen(int(sys.argv[2]) if len(sys.argv) > 2 else 60)
    else:
        check(int(sys.argv[2]) if len(sys.argv) > 2 else 3)
