#!/usr/bin/env python3
"""Generates data/languages/e200_lsp.sinc, the e200z4 Lightweight Signal
Processing APU (LSP), from tools/lsp_opcodes.txt.

The semantics follow the pseudo-RTL of the NXP "Lightweight Signal Processing
APU Reference Manual" Rev. 3 (LSPAPURM), section 1.6. Section numbers in the
comments below refer to that manual.

usage: gen_lsp.py [--check]
  --check  exit with status 1 if e200_lsp.sinc is not up to date
"""
import pathlib
import re
import sys

TOOLS = pathlib.Path(__file__).resolve().parent
TABLE = TOOLS / 'lsp_opcodes.txt'
OUT = TOOLS.parent / 'data' / 'languages' / 'e200_lsp.sinc'

INT32_MIN, INT32_MAX = -(1 << 31), (1 << 31) - 1
INT16_MIN, INT16_MAX = -(1 << 15), (1 << 15) - 1


def const(value, size):
    return f'0x{value & ((1 << (8 * size)) - 1):x}'


def H(reg):
    """Even (upper) halfword of a 32-bit register."""
    return f'{reg}[16,16]'


def L(reg):
    """Odd (lower) halfword of a 32-bit register."""
    return f'{reg}:2'


class Sem:
    """P-code of one constructor."""

    def __init__(self):
        self.lines = []
        self.count = 0
        self.pair = False       # rD:rD+1 (or rS:rS+1) is an operand
        self.ov = []            # overflow flags recorded in SPEFSCR OV/SOV

    def __call__(self, *lines):
        self.lines.extend(lines)

    def name(self, base):
        self.count += 1
        return f'{base}{self.count}'

    def spefscr(self):
        """SPEFSCR[OV] = ov; SPEFSCR[SOV] |= ov."""
        if not self.ov:
            return
        self(f'local ov:1 = {" || ".join(self.ov)};',
             'local ovbits:4 = zext(ov) * 0xc000;',
             'spr200 = (spr200 & 0xffffbfff) | ovbits;')


def clamp(s, dst, val, lo, hi, size, value, lo_out, hi_out, flag=True):
    """dst = value, or hi_out/lo_out when the signed 'size'-byte val is above
    hi/below lo. Records the overflow flag unless flag is False."""
    p, n = s.name('above'), s.name('below')
    s(f'local {p}:1 = {val} s> {const(hi, size)};',
      f'local {n}:1 = {val} s< {const(lo, size)};',
      f'{dst} = {value};')
    for cond, out in ((p, hi_out), (n, lo_out)):
        label = s.name('in_range')
        s(f'if (!{cond}) goto <{label}>;', f'{dst} = {out};', f'<{label}>')
    if flag:
        s.ov.append(f'{p} || {n}')


def pack(s, dst, hi, lo):
    s(f'{dst} = (zext({hi}) << 16) | zext({lo});')


def pair_value(s, name='acc'):
    s(f'local {name}:8 = (zext(D) << 32) | zext(Dodd);')
    return name


def set_pair(s, value):
    s(f'D = {value}(4);', f'Dodd = {value}:4;')


def mul16(s, name, a, b, ty):
    """32-bit product of two halfwords. ty: ui, si or sui (signed a, unsigned b)."""
    e1 = 'zext' if ty == 'ui' else 'sext'
    e2 = 'sext' if ty == 'si' else 'zext'
    s(f'local {name}:4 = {e1}({a}) * {e2}({b});')
    return name


def sf16(s, name, a, b, special=None):
    """1.31 product of two 1.15 halfwords. -1.0 * -1.0 gives 'special'."""
    s(f'local {name}:4 = (sext({a}) * sext({b})) << 1;')
    if special is not None:
        label = s.name('not_minus_one')
        s(f'if (({a} != 0x8000) || ({b} != 0x8000)) goto <{label}>;',
          f'{name} = {special};',
          f'<{label}>')
    return name


def sf16_wide(s, name, a, b):
    """Exact 2*a*b of two 1.15 halfwords; -1.0 * -1.0 is +1.0 (0x80000000)."""
    s(f'local {name}:8 = (sext({a}) * sext({b})) << 1;')
    return name


def ext_for(ty):
    return 'zext' if ty in ('u', 'ui') else 'sext'


def op_for(acc):
    return '+' if acc == 'aa' else '-'


# ---------------------------------------------------------------------------
# Element selection

def sel_zmh(hs):
    """zmh{e,eo,o}: (src1, src2)."""
    return {'e': (H('A'), H('B')), 'eo': (H('A'), L('B')), 'o': (L('A'), L('B'))}[hs]


def sel_zvmh(hs):
    """zvmh{ul,ll,uu,xl}: ((src1h, src2h), (src1l, src2l)), 1.6.5.28."""
    return {
        'ul': ((H('A'), H('B')), (L('A'), L('B'))),
        'll': ((L('A'), H('B')), (L('A'), L('B'))),
        'uu': ((H('A'), H('B')), (H('A'), L('B'))),
        'xl': ((L('A'), L('B')), (H('A'), L('B'))),
    }[hs]


def sel_dot(x):
    """zvdotph[x]: ((src1h, src2h), (src1l, src2l)), 1.6.5.36."""
    if x:
        return (L('A'), H('B')), (H('A'), L('B'))
    return (H('A'), H('B')), (L('A'), L('B'))


def unsigned_ty(ty):
    return ty in ('u', 'ui')


def ty_of(t):
    """s/su/u mnemonic part to si/sui/ui."""
    return {'s': 'si', 'su': 'sui', 'u': 'ui', 'si': 'si', 'sui': 'sui', 'ui': 'ui'}[t]


# ---------------------------------------------------------------------------
# Multiply and dot product families, 1.6.5

def zmh_guarded(s, m):
    """1.6.5.1-2 zmh{e,eo,o}g{si,ui,sui,smf}[{aa,an}]: 16x16 -> 64 in rD:rD+1."""
    hs, ty, acc = m.groups()
    a, b = sel_zmh(hs)
    s.pair = True
    if ty == 'smf':
        sf16_wide(s, 'prod', a, b)
    else:
        mul16(s, 'p32', a, b, ty)
        s(f'local prod:8 = {ext_for(ty)}(p32);')
    if acc:
        pair_value(s)
        s(f'acc = acc {op_for(acc)} prod;')
        set_pair(s, 'acc')
    else:
        set_pair(s, 'prod')


def to_9_23(s, name, wide, r):
    """Round or truncate a wide 1.31 (or 2.31) value to 9.23 in 32 bits."""
    if r:
        s(f'{wide} = {wide} + 0x80;')
    s(f'local {name}_s:8 = {wide} s>> 8;', f'local {name}:4 = {name}_s:4;')
    return name


def zmh_gw(s, m):
    """1.6.5.3-4 zmh{e,eo,o}gwsmf[r][{aa,an}]: 9.23 product in rD."""
    hs, r, acc = m.groups()
    a, b = sel_zmh(hs)
    sf16_wide(s, 'prod', a, b)
    to_9_23(s, 'g', 'prod', r)
    s(f'D = D {op_for(acc)} g;' if acc else 'D = g;')


def zmh_sf(s, m):
    """1.6.5.5 zmh{e,eo,o}sf[r]."""
    hs, r = m.groups()
    a, b = sel_zmh(hs)
    sf16(s, 'prod', a, b)
    if r:
        s('prod = (prod + 0x8000) & 0xffff0000;')
    label = s.name('not_minus_one')
    s(f'if (({a} != 0x8000) || ({b} != 0x8000)) goto <{label}>;',
      f'prod = {"0x7fff0000" if r else "0x7fffffff"};',
      f'<{label}>',
      'D = prod;')


def acc_sat32(s, dst, acc_expr, prod, op, r, ty='si', dst_is=None):
    """dst = saturate32(acc op prod) with optional rounding to 16 bits.
    acc_expr and prod are signed (or unsigned for ty ui) 32-bit values."""
    ext = ext_for(ty)
    t = s.name('sum')
    s(f'local {t}:8 = {ext}({acc_expr}) {op} {ext}({prod});')
    if r:
        s(f'{t} = ({t} + 0x8000) & 0xffffffffffff0000;')
    if unsigned_ty(ty):
        clamp(s, dst, t, 0, 0xffffffff, 8, f'{t}:4', '0', '0xffffffff')
    else:
        clamp(s, dst, t, INT32_MIN, INT32_MAX, 8, f'{t}:4', '0x80000000',
              '0x7fff0000' if r else '0x7fffffff')


def zmh_sf_acc(s, m):
    """1.6.5.6 zmh{e,eo,o}sf[r]{aa,an}s."""
    hs, r, acc = m.groups()
    a, b = sel_zmh(hs)
    sf16(s, 'prod', a, b, '0x7fffffff')
    acc_sat32(s, 'D', 'D', 'prod', op_for(acc), r)


def zmh_int(s, m):
    """1.6.5.7-9 zmh{e,eo,o}{s,su,u}i[{aa,an}[s]]."""
    hs, ty, acc, sat = m.groups()
    a, b = sel_zmh(hs)
    mul16(s, 'prod', a, b, ty_of(ty))
    if not acc:
        s('D = prod;')
    elif not sat:
        s(f'D = D {op_for(acc)} prod;')
    else:
        acc_sat32(s, 'D', 'D', 'prod', op_for(acc), False, ty_of(ty))


def zvmhsfh(s, m):
    """1.6.5.10-11 zvmhsfh, zvmhsfrh."""
    (r,) = m.groups()
    halves = []
    for x, src in (('h', H), ('l', L)):
        p = sf16(s, f'prod{x}', src('A'), src('B'))
        if r:
            s(f'{p} = {p} + 0x8000;')
        label = s.name('not_minus_one')
        s(f'if (({src("A")} != 0x8000) || ({src("B")} != 0x8000)) goto <{label}>;',
          f'{p} = {"0x7fff0000" if r else "0x7fffffff"};',
          f'<{label}>')
        halves.append(f'{p}[16,16]')
    pack(s, 'D', *halves)


def zvmhsf_acc(s, m):
    """1.6.5.12 zvmhsf[r]{aa,an}hs."""
    r, acc = m.groups()
    halves = []
    for x, src in (('h', H), ('l', L)):
        p = sf16(s, f'prod{x}', src('A'), src('B'), '0x7fffffff')
        s(f'local sum{x}:8 = (sext({src("D")}) << 16) {op_for(acc)} sext({p});')
        if r:
            s(f'sum{x} = (sum{x} + 0x8000) & 0xffffffffffff0000;')
        s(f'local hi{x}:8 = sum{x} >> 16;', f'local res{x}:2 = hi{x}:2;')
        clamp(s, f'res{x}', f'sum{x}', INT32_MIN, INT32_MAX, 8, f'hi{x}:2',
              '0x8000', '0x7fff')
        halves.append(f'res{x}')
    pack(s, 'D', *halves)


def zvmh_int_h(s, m):
    """1.6.5.13-16 zvmh{s,su,u}i[{aa,an}]h[s]."""
    ty, acc, sat = m.groups()
    ty = ty_of(ty)
    halves = []
    for x, src in (('h', H), ('l', L)):
        p = mul16(s, f'prod{x}', src('A'), src('B'), ty)
        if not sat:
            if acc:
                s(f'local res{x}:2 = {src("D")} {op_for(acc)} {p}:2;')
            else:
                s(f'local res{x}:2 = {p}:2;')
        else:
            ext = ext_for(ty)
            s(f'local sum{x}:8 = {ext}({p});')
            if acc:
                s(f'sum{x} = {ext}({src("D")}) {op_for(acc)} sum{x};')
            s(f'local res{x}:2 = sum{x}:2;')
            if unsigned_ty(ty):
                clamp(s, f'res{x}', f'sum{x}', 0, 0xffff, 8, f'sum{x}:2', '0', '0xffff')
            else:
                clamp(s, f'res{x}', f'sum{x}', INT16_MIN, INT16_MAX, 8, f'sum{x}:2',
                      '0x8000', '0x7fff')
        halves.append(f'res{x}')
    pack(s, 'D', *halves)


def zmwg_int(s, m):
    """1.6.5.17-19 zmwg{s,u,su}i[{aa,an}[s]]: 32x32 -> 64 in rD:rD+1."""
    ty, acc, sat = m.groups()
    s.pair = True
    e1 = 'zext' if ty == 'u' else 'sext'
    e2 = 'sext' if ty == 's' else 'zext'
    s(f'local prod:8 = {e1}(A) * {e2}(B);')
    if not acc:
        set_pair(s, 'prod')
        return
    pair_value(s)
    op = op_for(acc)
    if not sat:
        s(f'acc = acc {op} prod;')
        set_pair(s, 'acc')
        return
    s(f'local res:8 = acc {op} prod;')
    if ty == 'u':
        if op == '+':
            s('local ovf:1 = carry(acc, prod);')
            sat_value = '0xffffffffffffffff'
        else:
            s('local ovf:1 = acc < prod;')
            sat_value = '0'
    else:
        s(f'local ovf:1 = {"scarry" if op == "+" else "sborrow"}(acc, prod);')
        # an overflowing result has the sign of acc
        s('local satv:8 = 0x7fffffffffffffff + zext(acc s< 0);')
        sat_value = 'satv'
    label = s.name('no_overflow')
    s(f'if (!ovf) goto <{label}>;', f'res = {sat_value};', f'<{label}>')
    set_pair(s, 'res')
    s.ov.append('ovf')


def zmwgsmf(s, m):
    """1.6.5.20-21 zmwgsmf[r][{aa,an}]: 17.47 product in rD:rD+1."""
    r, acc = m.groups()
    s.pair = True
    s('local prod:8 = (sext(A) * sext(B)) << 1;')
    if r:
        s('prod = prod + 0x8000;')
    s('local g:8 = prod s>> 16;')
    label = s.name('not_minus_one')
    s('if ((A != 0x80000000) || (B != 0x80000000)) goto <%s>;' % label,
      'g = 0x800000000000;',
      f'<{label}>')
    if acc:
        pair_value(s)
        s(f'acc = acc {op_for(acc)} g;')
        set_pair(s, 'acc')
    else:
        set_pair(s, 'g')


def zmwl_sat(s, m):
    """1.6.5.22-23 zmwl{s,su,u}is: 32x32 saturated to 32 bits."""
    (ty,) = m.groups()
    e1 = 'zext' if ty == 'u' else 'sext'
    e2 = 'sext' if ty == 's' else 'zext'
    s(f'local prod:8 = {e1}(A) * {e2}(B);')
    if ty == 'u':
        s('local ovf:1 = prod > 0xffffffff;', 'D = prod:4;')
        label = s.name('in_range')
        s(f'if (!ovf) goto <{label}>;', 'D = 0xffffffff;', f'<{label}>')
        s.ov.append('ovf')
    else:
        clamp(s, 'D', 'prod', INT32_MIN, INT32_MAX, 8, 'prod:4', '0x80000000', '0x7fffffff')


def zmwl_acc(s, m):
    """1.6.5.24-25 zmwl{s,su,u}i{aa,an}[s]."""
    ty, acc, sat = m.groups()
    op = op_for(acc)
    if not sat:
        s(f'D = D {op} (A * B);')
        return
    e1 = 'zext' if ty == 'u' else 'sext'
    e2 = 'sext' if ty == 's' else 'zext'
    s(f'local prod:8 = {e1}(A) * {e2}(B);')
    if ty == 'u':
        # the 65-bit sum saturates to [0, 0xffffffff]
        if op == '+':
            s('local sum:4 = D + prod:4;',
              'local ovf:1 = (prod > 0xffffffff) || carry(D, prod:4);')
            out = '0xffffffff'
        else:
            s('local sum:4 = D - prod:4;',
              'local ovf:1 = prod > zext(D);')
            out = '0'
        s('D = sum;')
        label = s.name('in_range')
        s(f'if (!ovf) goto <{label}>;', f'D = {out};', f'<{label}>')
        s.ov.append('ovf')
    else:
        # the signed sum fits in 64 bits
        s(f'local sum:8 = sext(D) {op} prod;')
        clamp(s, 'D', 'sum', INT32_MIN, INT32_MAX, 8, 'sum:4', '0x80000000', '0x7fffffff')


def zmwsf(s, m):
    """1.6.5.26 zmwsf[r]."""
    (r,) = m.groups()
    s('local prod:8 = (sext(A) * sext(B)) << 1;')
    if r:
        s('prod = prod + 0x80000000;')
    s('D = prod(4);')
    label = s.name('not_minus_one')
    s(f'if ((A != 0x80000000) || (B != 0x80000000)) goto <{label}>;',
      'D = 0x7fffffff;',
      f'<{label}>')


def zmwsf_acc(s, m):
    """1.6.5.27 zmwsf[r]{aa,an}s: 66-bit accumulate, saturated to 32 bits.
    The sum is (rD << 32) op prod; it is computed as a 64-bit high part and a
    carry from the low part, which cannot overflow."""
    r, acc = m.groups()
    op = op_for(acc)
    s('local prod:8 = (sext(A) * sext(B)) << 1;')
    label = s.name('not_minus_one')
    s(f'if ((A != 0x80000000) || (B != 0x80000000)) goto <{label}>;',
      'prod = 0x7fffffffffffffff;',
      f'<{label}>',
      'local prodhi:4 = prod(4);',
      'local prodlo:4 = prod:4;',
      f'local high:8 = sext(D) {op} sext(prodhi);',
      f'local low:8 = {"" if op == "+" else "-"}zext(prodlo);')
    if r:
        s('low = low + 0x80000000;')
    s('high = high + (low s>> 32);')
    clamp(s, 'D', 'high', INT32_MIN, INT32_MAX, 8, 'high:4', '0x80000000', '0x7fffffff')


ACC_OPS = {'aa': ('+', '+'), 'an': ('-', '-'), 'anp': ('-', '+')}


def zvmh_gw(s, m):
    """1.6.5.28-29 zvmh{ul,ll,uu,xl}gwsmf[r][{aa,an,anp}]: 9.23 in rD, rD+1."""
    hs, r, acc = m.groups()
    s.pair = True
    for (a, b), x, dst in zip(sel_zvmh(hs), 'hl', ('D', 'Dodd')):
        sf16_wide(s, f'prod{x}', a, b)
        to_9_23(s, f'g{x}', f'prod{x}', r)
    for x, dst, op in zip('hl', ('D', 'Dodd'), ACC_OPS[acc] if acc else (None, None)):
        s(f'{dst} = {dst} {op} g{x};' if op else f'{dst} = g{x};')


def zvmh_sf(s, m):
    """1.6.5.30 zvmh{ul,ll,uu,xl}sf[r]: 1.31 in rD, rD+1."""
    hs, r = m.groups()
    s.pair = True
    for (a, b), x, dst in zip(sel_zvmh(hs), 'hl', ('D', 'Dodd')):
        p = sf16(s, f'prod{x}', a, b)
        if r:
            s(f'{p} = ({p} + 0x8000) & 0xffff0000;')
        label = s.name('not_minus_one')
        s(f'if (({a} != 0x8000) || ({b} != 0x8000)) goto <{label}>;',
          f'{p} = {"0x7fff0000" if r else "0x7fffffff"};',
          f'<{label}>')
    s('D = prodh;', 'Dodd = prodl;')


def zvmh_sf_acc(s, m):
    """1.6.5.31-32 zvmh{ul,ll,uu,xl}sf[r]{aa,an,anp}s."""
    hs, r, acc = m.groups()
    s.pair = True
    for (a, b), x in zip(sel_zvmh(hs), 'hl'):
        sf16(s, f'prod{x}', a, b, '0x7fffffff')
    for x, dst, op in zip('hl', ('D', 'Dodd'), ACC_OPS[acc]):
        s(f'local res{x}:4 = 0;')
        acc_sat32(s, f'res{x}', dst, f'prod{x}', op, r)
    s('D = resh;', 'Dodd = resl;')


def zvmh_int(s, m):
    """1.6.5.33-35 zvmh{ul,ll,uu,xl}{s,su,u}i[{aa,an,anp}[s]]."""
    hs, ty, acc, sat = m.groups()
    ty = ty_of(ty)
    s.pair = True
    for (a, b), x in zip(sel_zvmh(hs), 'hl'):
        mul16(s, f'prod{x}', a, b, ty)
    if not acc:
        s('D = prodh;', 'Dodd = prodl;')
        return
    if not sat:
        oh, ol = ACC_OPS[acc]
        s(f'D = D {oh} prodh;', f'Dodd = Dodd {ol} prodl;')
        return
    for x, dst, op in zip('hl', ('D', 'Dodd'), ACC_OPS[acc]):
        s(f'local res{x}:4 = 0;')
        acc_sat32(s, f'res{x}', dst, f'prod{x}', op, False, ty)
    s('D = resh;', 'Dodd = resl;')


def zvdotph_g(s, m):
    """1.6.5.36-39 zvdotph[x]g{a,s}{si,ui,sui,smf}[{aa,an}]: 64-bit in rD:rD+1."""
    x, sub, ty, acc = m.groups()
    s.pair = True
    for (a, b), e in zip(sel_dot(x), 'hl'):
        if ty == 'smf':
            sf16_wide(s, f'prod{e}', a, b)
        else:
            mul16(s, f'p{e}', a, b, ty)
            s(f'local prod{e}:8 = {ext_for(ty)}(p{e});')
    s(f'local dot:8 = prodh {"-" if sub == "s" else "+"} prodl;')
    if acc:
        pair_value(s)
        s(f'acc = acc {op_for(acc)} dot;')
        set_pair(s, 'acc')
    else:
        set_pair(s, 'dot')


def zvdotph_sf(s, m):
    """1.6.5.40-41, 46-47 zvdotph{[x]a,s}sf[r][{aa,an}]s."""
    x, sub, r, acc = m.groups()
    for (a, b), e in zip(sel_dot(x), 'hl'):
        sf16(s, f'prod{e}', a, b, '0x7fffffff')
    op = '-' if sub == 's' else '+'
    s(f'local dot:8 = sext(prodh) {op} sext(prodl);')
    if acc:
        s(f'dot = sext(D) {op_for(acc)} dot;')
    if r:
        s('dot = (dot + 0x8000) & 0xffffffffffff0000;')
    clamp(s, 'D', 'dot', INT32_MIN, INT32_MAX, 8, 'dot:4', '0x80000000',
          '0x7fff0000' if r else '0x7fffffff')


def zvdotph_int(s, m):
    """1.6.5.42-45, 48-51 zvdotph{[x]a,s}{si,ui,sui}[{aa,an}][s]."""
    x, sub, ty, acc, sat = m.groups()
    for (a, b), e in zip(sel_dot(x), 'hl'):
        mul16(s, f'prod{e}', a, b, ty)
    op = '-' if sub == 's' else '+'
    if not sat:
        if acc:
            s(f'D = D {op_for(acc)} (prodh {op} prodl);')
        else:
            s(f'D = prodh {op} prodl;')
        return
    ext = ext_for(ty)
    s(f'local dot:8 = {ext}(prodh) {op} {ext}(prodl);')
    if acc:
        s(f'dot = {ext}(D) {op_for(acc)} dot;')
    if unsigned_ty(ty):
        clamp(s, 'D', 'dot', 0, 0xffffffff, 8, 'dot:4', '0', '0xffffffff')
    else:
        clamp(s, 'D', 'dot', INT32_MIN, INT32_MAX, 8, 'dot:4', '0x80000000', '0x7fffffff')


def zvdotph_gw(s, m):
    """1.6.5.52-55 zvdotph{[x]gwa,gws}smf[r][{aa,an}]: 9.23 result in rD."""
    x, sub, r, acc = m.groups()
    for (a, b), e in zip(sel_dot(x), 'hl'):
        sf16_wide(s, f'prod{e}', a, b)
    s(f'local dot:8 = prodh {"-" if sub == "s" else "+"} prodl;')
    to_9_23(s, 'g', 'dot', r)
    s(f'D = D {op_for(acc)} g;' if acc else 'D = g;')


# ---------------------------------------------------------------------------
# Simple instructions, 1.6.3

def bitrev16(s, dst, src):
    s(f'local {dst}:2 = (({src} >> 1) & 0x5555) | (({src} & 0x5555) << 1);',
      f'{dst} = (({dst} >> 2) & 0x3333) | (({dst} & 0x3333) << 2);',
      f'{dst} = (({dst} >> 4) & 0x0f0f) | (({dst} & 0x0f0f) << 4);',
      f'{dst} = ({dst} >> 8) | ({dst} << 8);')


def zbrminc(s, m):
    """1.6.3.1: bit-reversed increment of rA[48:63] under the mask in rB (16 bits)."""
    s('local mask:2 = B:2;', 'local bits:2 = A:2 | ~mask;')
    bitrev16(s, 'rev', 'bits')
    s('rev = rev + 1;')
    bitrev16(s, 'inc', 'rev')
    s('local low:2 = (A:2 & ~mask) | (inc & mask);',
      'D = (A & 0xffff0000) | zext(low);')


def circular(s, dst, base, offset):
    """Circular increment of the index base[51:63] (1.6.2.2, 1.6.3.2).
    offset is the biased signed offset: offsets >= 0 add offset + 1.
    The index wraps when it passes the last byte of the buffer, whose
    length in doublewords - 1 is base[41:50]."""
    s(f'local last:4 = ((({base} >> 13) & 0x3ff) << 3) | 7;',
      f'local index:4 = ({base} & 0x1fff) + {offset} + zext({offset} s>= 0);')
    end, done = s.name('before_end'), s.name('wrapped')
    s(f'if (index s<= last) goto <{end}>;',
      'index = index - (last + 1);',
      f'goto <{done}>;',
      f'<{end}>',
      f'if (index s>= 0) goto <{done}>;',
      'index = index + (last + 1);',
      f'<{done}>',
      f'{dst} = ({base} & 0xffffe000) | (index & 0x1fff);')


def zcircinc(s, m):
    """1.6.3.2: the offset is rB[50:63]."""
    s('local offset:4 = (B << 18) s>> 18;')
    circular(s, 'D', 'A', 'offset')


def abs16(s, dst, src, sat):
    label = s.name('positive')
    s(f'local {dst}:2 = {src};')
    if sat:
        s(f'local ov{dst}:1 = {dst} == 0x8000;')
        s.ov.append(f'ov{dst}')
    s(f'if ({dst} s>= 0) goto <{label}>;', f'{dst} = -{dst};')
    if sat:
        s(f'{dst} = {dst} - zext(ov{dst});')
    s(f'<{label}>')


def zvabsh(s, m):
    """1.6.3.3-4 zvabsh[s]."""
    (sat,) = m.groups()
    abs16(s, 'resh', H('A'), sat)
    abs16(s, 'resl', L('A'), sat)
    pack(s, 'D', 'resh', 'resl')


def zabsw(s, m):
    """1.6.3.5-6 zabsw[s]."""
    (sat,) = m.groups()
    label = s.name('positive')
    s('local res:4 = A;')
    if sat:
        s('local ovf:1 = res == 0x80000000;')
        s.ov.append('ovf')
    s(f'if (res s>= 0) goto <{label}>;', 'res = -res;')
    if sat:
        s('res = res - zext(ovf);')
    s(f'<{label}>', 'D = res;')


def sat_ops16(s, x, a, b, op, sat):
    """16-bit a op b; sat: None (modulo), 'ss' (signed) or 'us' (unsigned)."""
    if not sat:
        s(f'local res{x}:2 = {a} {op} {b};')
        return f'res{x}'
    ext = 'sext' if sat == 'ss' else 'zext'
    s(f'local sum{x}:4 = {ext}({a}) {op} {ext}({b});', f'local res{x}:2 = sum{x}:2;')
    if sat == 'ss':
        clamp(s, f'res{x}', f'sum{x}', INT16_MIN, INT16_MAX, 4, f'sum{x}:2', '0x8000', '0x7fff')
    else:
        clamp(s, f'res{x}', f'sum{x}', 0, 0xffff, 4, f'sum{x}:2', '0', '0xffff')
    return f'res{x}'


# rD[h], rD[l] = rB[h] oph rA[hsel], rB[l] opl rA[lsel] (x: rA halves exchanged)
VEC_H = {
    'zvaddh': ('+', '+', False), 'zvsubfh': ('-', '-', False),
    'zvaddsubfh': ('+', '-', False), 'zvsubfaddh': ('-', '+', False),
    'zvaddhx': ('+', '+', True), 'zvsubfhx': ('-', '-', True),
    'zvaddsubfhx': ('+', '-', True), 'zvsubfaddhx': ('-', '+', True),
}


def zvh_arith(s, m):
    """1.6.3.10-19, 91-94, 98, 103-106: halfword add/subtract [saturate]."""
    base, sat = m.groups()
    oph, opl, x = VEC_H[base]
    ah, al = (L('A'), H('A')) if x else (H('A'), L('A'))
    rh = sat_ops16(s, 'h', H('B'), ah, oph, sat)
    rl = sat_ops16(s, 'l', L('B'), al, opl, sat)
    pack(s, 'D', rh, rl)


def zvaddih(s, m):
    """1.6.3.15, 117 zvaddih, zvsubifh."""
    (op,) = m.groups()
    op = '+' if op == 'add' else '-'
    s(f'local resh:2 = {H("A")} {op} EVUIMM;', f'local resl:2 = {L("A")} {op} EVUIMM;')
    pack(s, 'D', 'resh', 'resl')


def zaddh_w(s, m):
    """1.6.3.20-23, 99-102 z{add,subf}h{e,o}{s,u}w."""
    op, eo, su = m.groups()
    src = H if eo == 'e' else L
    ext = 'sext' if su == 's' else 'zext'
    s(f'D = {ext}({src("B")}) {"+" if op == "add" else "-"} {ext}({src("A")});')


def sat_word(s, dst, a, b, op, sat):
    """32-bit a op b, saturating signed ('ss') or unsigned ('us')."""
    ext = 'sext' if sat == 'ss' else 'zext'
    t = s.name('sum')
    s(f'local {t}:8 = {ext}({a}) {op} {ext}({b});')
    if sat == 'ss':
        clamp(s, dst, t, INT32_MIN, INT32_MAX, 8, f'{t}:4', '0x80000000', '0x7fffffff')
    else:
        clamp(s, dst, t, 0, 0xffffffff, 8, f'{t}:4', '0', '0xffffffff')


VEC_W = {'zvaddw': ('+', '+'), 'zvsubfw': ('-', '-'),
         'zvaddsubfw': ('+', '-'), 'zvsubfaddw': ('-', '+')}


def zvw_arith(s, m):
    """1.6.3.24-26, 31, 33, 107-109, 114, 116: rD op= rA, rD+1 op= rB."""
    base, sat = m.groups()
    s.pair = True
    oph, opl = VEC_W[base]
    if not sat:
        s(f'D = D {oph} A;', f'Dodd = Dodd {opl} B;')
        return
    s('local resh:4 = 0;', 'local resl:4 = 0;')
    sat_word(s, 'resh', 'D', 'A', oph, sat)
    sat_word(s, 'resl', 'Dodd', 'B', opl, sat)
    s('D = resh;', 'Dodd = resl;')


def zaddw_sat(s, m):
    """1.6.3.30, 32, 113, 115 z{add,subf}w{s,u}s: rB op rA."""
    op, sat = m.groups()
    sat_word(s, 'D', 'B', 'A', '+' if op == 'add' else '-', sat)


def zaddwg(s, m):
    """1.6.3.27-29, 110-112 z{add,subf}wg{sf,si,ui}: 64-bit rB op rA in rD:rD+1."""
    op, ty = m.groups()
    s.pair = True
    ext = 'zext' if ty == 'ui' else 'sext'
    s(f'local wa:8 = {ext}(A);', f'local wb:8 = {ext}(B);')
    if ty == 'sf':
        s('wa = wa << 16;', 'wb = wb << 16;')
    s(f'local res:8 = wb {"+" if op == "add" else "-"} wa;')
    set_pair(s, 'res')


def zaddd(s, m):
    """1.6.3.7-9, 95-97 z{add,subf}d[{ss,us}]: rD:rD+1 op rA:rB."""
    op, sat = m.groups()
    s.pair = True
    op = '+' if op == 'add' else '-'
    pair_value(s)
    s('local val:8 = (zext(A) << 32) | zext(B);', f'local res:8 = acc {op} val;')
    if sat:
        if sat == 'us':
            s(f'local ovf:1 = {"carry(acc, val)" if op == "+" else "acc < val"};')
            out = '0xffffffffffffffff' if op == '+' else '0'
        else:
            s(f'local ovf:1 = {"scarry" if op == "+" else "sborrow"}(acc, val);',
              'local satv:8 = 0x7fffffffffffffff + zext(acc s< 0);')
            out = 'satv'
        label = s.name('no_overflow')
        s(f'if (!ovf) goto <{label}>;', f'res = {out};', f'<{label}>')
        s.ov.append('ovf')
    set_pair(s, 'res')


def zvcmp(s, m):
    """1.6.3.34-38: CR field = ch || cl || ch|cl || ch&cl."""
    (kind,) = m.groups()
    op = {'eqh': '==', 'gths': 's>', 'gthu': '>', 'lths': 's<', 'lthu': '<'}[kind]
    s(f'local ch:1 = {H("A")} {op} {H("B")};',
      f'local cl:1 = {L("A")} {op} {L("B")};',
      'CRFD = (ch << 3) | (cl << 2) | ((ch | cl) << 1) | (ch & cl);')


def zcnt(s, m):
    """1.6.3.39-41 zvcntlsh, zcntlsw, zvcntlzh. Leading sign bits include the
    sign bit itself, as for evcntlsw."""
    name = m.group(0)
    if name == 'zcntlsw':
        s('local bits:4 = A ^ (A s>> 31);', 'D = lzcount(bits);')
        return
    for x, src in (('h', H), ('l', L)):
        if name == 'zvcntlsh':
            s(f'local bits{x}:2 = {src("A")} ^ ({src("A")} s>> 15);')
        else:
            s(f'local bits{x}:2 = {src("A")};')
        s(f'local res{x}:2 = lzcount(bits{x});')
    pack(s, 'D', 'resh', 'resl')


def zdivwsf(s, m):
    """1.6.3.42: signed fractional divide with saturation."""
    s('local dividend:8 = sext(A);', 'local divisor:8 = sext(B);')
    for v in ('dividend', 'divisor'):
        label = s.name('positive')
        s(f'local abs{v}:8 = {v};', f'if ({v} s>= 0) goto <{label}>;',
          f'abs{v} = -{v};', f'<{label}>')
    same, divide, done = s.name('same_sign'), s.name('divide'), s.name('done')
    s('local ovf:1 = 1;',
      f'if ((A ^ B) s>= 0) goto <{same}>;',
      f'if ((absdividend s<= absdivisor) && (divisor != 0)) goto <{divide}>;',
      'D = 0x80000000;',
      f'goto <{done}>;',
      f'<{same}>',
      f'if ((absdividend s< absdivisor) && (divisor != 0)) goto <{divide}>;',
      'D = 0x7fffffff;',
      f'goto <{done}>;',
      f'<{divide}>',
      'local quotient:8 = (dividend << 31) s/ divisor;',
      'D = quotient:4;',
      'ovf = 0;',
      f'<{done}>')
    s.ov.append('ovf')


MERGE = {'hih': (H, H), 'hiloh': (H, L), 'loh': (L, L), 'lohih': (L, H)}


def zvmerge(s, m):
    """1.6.3.43-46."""
    ha, hb = MERGE[m.group(1)]
    pack(s, 'D', ha('A'), hb('B'))


def zvneg(s, m):
    """1.6.3.47-50 zvnegh[s], zvnegho[s]."""
    odd, sat = m.groups()
    halves = []
    for x, src in (('h', H), ('l', L)):
        if odd and x == 'h':
            halves.append(src('A'))
            continue
        s(f'local res{x}:2 = -{src("A")};')
        if sat:
            s(f'local ov{x}:1 = {src("A")} == 0x8000;', f'res{x} = res{x} - zext(ov{x});')
            s.ov.append(f'ov{x}')
        halves.append(f'res{x}')
    pack(s, 'D', *halves)


def znegws(s, m):
    """1.6.3.51."""
    s('local ovf:1 = A == 0x80000000;', 'D = -A - zext(ovf);')
    s.ov.append('ovf')


def zvpkshgwshfrs(s, m):
    """1.6.3.52: 9.23 words in rA, rB to 1.15 halfwords, rounded, saturated."""
    halves = []
    for x, src in (('h', 'A'), ('l', 'B')):
        s(f'local rnd{x}:8 = (sext({src}) + 0x80) s>> 8;', f'local res{x}:2 = rnd{x}:2;')
        clamp(s, f'res{x}', f'rnd{x}', INT16_MIN, INT16_MAX, 8, f'rnd{x}:2', '0x8000', '0x7fff')
        halves.append(f'res{x}')
    pack(s, 'D', *halves)


def zpkswg(s, m):
    """1.6.3.53-54 zpkswgshfrs, zpkswgswfrs: 17.47 in rA:rB, rounded, saturated."""
    (dst,) = m.groups()
    s('local val:8 = (zext(A) << 32) | zext(B);')
    if dst == 'sh':
        # to 1.15 in the upper halfword; the rounding add cannot overflow in range
        s('local above:1 = val s>= 0x7fff80000000;',
          'local below:1 = val s< 0xffff7fff80000000;',
          'local rnd:8 = (val + 0x80000000) s>> 32;',
          'D = zext(rnd:2) << 16;')
        hi, lo = '0x7fff0000', '0x80000000'
    else:
        s('local above:1 = val s>= 0x7fffffff8000;',
          'local below:1 = val s< 0xffff7fffffff8000;',
          'local rnd:8 = (val + 0x8000) s>> 16;',
          'D = rnd:4;')
        hi, lo = '0x7fffffff', '0x80000000'
    for cond, out in (('above', hi), ('below', lo)):
        label = s.name('in_range')
        s(f'if (!{cond}) goto <{label}>;', f'D = {out};', f'<{label}>')
    s.ov.append('above || below')


def zvpkswshfrs(s, m):
    """1.6.3.55: 1.31 words in rA, rB to 1.15 halfwords, rounded, saturated."""
    halves = []
    for x, src in (('h', 'A'), ('l', 'B')):
        s(f'local rnd{x}:8 = (sext({src}) + 0x8000) s>> 16;', f'local res{x}:2 = rnd{x}:2;')
        clamp(s, f'res{x}', f'rnd{x}', INT16_MIN, INT16_MAX, 8, f'rnd{x}:2', '0x8000', '0x7fff')
        halves.append(f'res{x}')
    pack(s, 'D', *halves)


def zvpk_sat(s, m):
    """1.6.3.56-58 zvpk{sw,uw}{s,u}hs: words in rA, rB to saturated halfwords."""
    src_t, dst_t = m.groups()
    ext = 'sext' if src_t == 's' else 'zext'
    lo, hi, lo_out, hi_out = ((INT16_MIN, INT16_MAX, '0x8000', '0x7fff') if dst_t == 's'
                              else (0, 0xffff, '0', '0xffff'))
    halves = []
    for x, src in (('h', 'A'), ('l', 'B')):
        s(f'local val{x}:8 = {ext}({src});', f'local res{x}:2 = {src}:2;')
        clamp(s, f'res{x}', f'val{x}', lo, hi, 8, f'{src}:2', lo_out, hi_out)
        halves.append(f'res{x}')
    pack(s, 'D', *halves)


def rotl16(s, x, src, n):
    s(f'local res{x}:2 = ({src} << {n}) | ({src} >> (16 - {n}));')


def zvrlh(s, m):
    """1.6.3.59-60 zvrlh, zvrlhi."""
    (imm,) = m.groups()
    for x, src in (('h', H), ('l', L)):
        if imm:
            n = 'EVUIMM'
        else:
            s(f'local n{x}:2 = {src("B")} & 0xf;')
            n = f'n{x}'
        rotl16(s, x, src('A'), n)
    pack(s, 'D', 'resh', 'resl')


def zrndwh(s, m):
    """1.6.3.61-62 zrndwh[ss]."""
    (sat,) = m.groups()
    s('D = (A + 0x8000) & 0xffff0000;')
    if sat:
        s('local ovf:1 = A s>= 0x7fff8000;')
        label = s.name('in_range')
        s(f'if (!ovf) goto <{label}>;', 'D = 0x7fff0000;', f'<{label}>')
        s.ov.append('ovf')


def zsat(s, m):
    """1.6.3.63-73 saturate instructions."""
    name = m.group(0)
    if name in ('zsatsdsw', 'zsatsduw'):
        s('local val:8 = (zext(A) << 32) | zext(B);')
        if name == 'zsatsdsw':
            clamp(s, 'D', 'val', INT32_MIN, INT32_MAX, 8, 'B', '0x80000000', '0x7fffffff')
        else:
            clamp(s, 'D', 'val', 0, 0xffffffff, 8, 'B', '0', '0xffffffff')
        return
    if name == 'zsatuduw':
        s('local ovf:1 = A != 0;', 'D = B;')
        label = s.name('in_range')
        s(f'if (!ovf) goto <{label}>;', 'D = 0xffffffff;', f'<{label}>')
        s.ov.append('ovf')
        return
    if name in ('zvsatshuh', 'zvsatuhsh'):
        for x, src in (('h', H), ('l', L)):
            s(f'local res{x}:2 = {src("A")};')
            if name == 'zvsatshuh':
                s(f'local ov{x}:1 = {src("A")} s< 0;')
                out = '0'
            else:
                s(f'local ov{x}:1 = {src("A")} > 0x7fff;')
                out = '0x7fff'
            label = s.name('in_range')
            s(f'if (!ov{x}) goto <{label}>;', f'res{x} = {out};', f'<{label}>')
            s.ov.append(f'ov{x}')
        pack(s, 'D', 'resh', 'resl')
        return
    # word to word/halfword: zsat{sw,uw}{sw,uw,sh,uh}
    src_t, dst = name[4:6], name[6:8]
    ext = 'sext' if src_t == 'sw' else 'zext'
    s(f'local val:8 = {ext}(A);')
    lo, hi = {'sw': (INT32_MIN, INT32_MAX), 'uw': (0, 0xffffffff),
              'sh': (INT16_MIN, INT16_MAX), 'uh': (0, 0xffff)}[dst]
    clamp(s, 'D', 'val', lo, hi, 8, 'A', const(lo, 4), const(hi, 4))


def zvselh(s, m):
    """1.6.3.74: select halfwords by cr0[LT], cr0[GT]."""
    s(f'local resh:2 = {H("B")};', f'local resl:2 = {L("B")};')
    for x, bit, src in (('h', 3, H), ('l', 2, L)):
        label = s.name('keep')
        s(f'if ((cr0 & {1 << bit}) == 0) goto <{label}>;', f'res{x} = {src("A")};', f'<{label}>')
    pack(s, 'D', 'resh', 'resl')


def zvsl_h(s, m):
    """1.6.3.75-80 zvslh[i][{us,ss}]: counts 0-31 (rB) or 0-15 (UIMM)."""
    imm, sat = m.groups()
    halves = []
    for x, src in (('h', H), ('l', L)):
        if imm:
            n = 'EVUIMM'
        else:
            s(f'local n{x}:8 = zext({src("B")} & 0x1f);')
            n = f'n{x}'
        if not sat:
            s(f'local res{x}:2 = {src("A")} << {n};')
        else:
            ext = 'sext' if sat == 'ss' else 'zext'
            s(f'local val{x}:8 = {ext}({src("A")}) << {n};', f'local res{x}:2 = val{x}:2;')
            if sat == 'ss':
                clamp(s, f'res{x}', f'val{x}', INT16_MIN, INT16_MAX, 8, f'val{x}:2',
                      '0x8000', '0x7fff')
            else:
                clamp(s, f'res{x}', f'val{x}', 0, 0xffff, 8, f'val{x}:2', '0', '0xffff')
        halves.append(f'res{x}')
    pack(s, 'D', *halves)


def zslw(s, m):
    """1.6.3.81-84 zslw[i]{ss,us}: counts 0-63 (rB) or 0-31 (UIMM). Counts
    above 32 give the same result as 32: overflow unless rA is 0."""
    imm, sat = m.groups()
    if imm:
        s('local n:8 = EVUIMM;')
    else:
        label = s.name('count_ok')
        s('local n:8 = zext(B & 0x3f);', f'if (n <= 32) goto <{label}>;', 'n = 32;', f'<{label}>')
    ext = 'sext' if sat == 'ss' else 'zext'
    s(f'local val:8 = {ext}(A) << n;')
    if sat == 'ss':
        clamp(s, 'D', 'val', INT32_MIN, INT32_MAX, 8, 'val:4', '0x80000000', '0x7fffffff')
    else:
        # zext(rA) << 32 can reach bit 63: compare unsigned
        label = s.name('in_range')
        s('local above:1 = val > 0xffffffff;', 'D = val:4;',
          f'if (!above) goto <{label}>;', 'D = 0xffffffff;', f'<{label}>')
        s.ov.append('above')


def zvsplat(s, m):
    """1.6.3.85-86 zvsplatfih, zvsplatih."""
    (frac,) = m.groups()
    if frac:
        s('local val:2 = A_BITSS << 11;')
    else:
        s('local val:2 = A_BITSS;')
    pack(s, 'D', 'val', 'val')


def zvsr_h(s, m):
    """1.6.3.87-90 zvsrh[i]{s,u}: counts 0-31 (rB) or 0-15 (UIMM)."""
    imm, su = m.groups()
    op = 's>>' if su == 's' else '>>'
    halves = []
    for x, src in (('h', H), ('l', L)):
        n = 'EVUIMM' if imm else f'({src("B")} & 0x1f)'
        s(f'local res{x}:2 = {src("A")} {op} {n};')
        halves.append(f'res{x}')
    pack(s, 'D', *halves)


def zunpk(s, m):
    """1.6.3.118-122 zvunpkh{gwsf,sf,si,ui}, zunpkwgsf."""
    name = m.group(0)
    s.pair = True
    if name == 'zunpkwgsf':
        s('local val:8 = sext(A) << 16;')
        set_pair(s, 'val')
        return
    for x, src, dst in (('h', H, 'D'), ('l', L, 'Dodd')):
        a = src('A')
        s({'zvunpkhgwsf': f'{dst} = sext({a}) << 8;',
           'zvunpkhsf': f'{dst} = zext({a}) << 16;',
           'zvunpkhsi': f'{dst} = sext({a});',
           'zvunpkhui': f'{dst} = zext({a});'}[name])


def zxtrw(s, m):
    """1.6.3.123: word at byte offset 1-3 of rA:rB."""
    s('local val:8 = (zext(A) << 32) | zext(B);',
      'local shift:8 = lspOffset * 8;',
      'val = val << shift;',
      'D = val(4);')


# ---------------------------------------------------------------------------
# Loads and stores, 1.6.4

def mem(ea, size, off=0):
    return f'*:{size} ({ea} + {off})' if off else f'*:{size} {ea}'


LOADS = {
    # name: (pair, access size of the immediate form, body)
    'zldd': (True, 8, lambda s, ea: (s(f'local val:8 = {mem(ea, 8)};'), set_pair(s, 'val'))),
    'zldw': (True, 8, lambda s, ea: s(f'D = {mem(ea, 4)};', f'Dodd = {mem(ea, 4, 4)};')),
    'zldh': (True, 8, lambda s, ea: s(
        f'D = (zext({mem(ea, 2)}) << 16) | zext({mem(ea, 2, 2)});',
        f'Dodd = (zext({mem(ea, 2, 4)}) << 16) | zext({mem(ea, 2, 6)});')),
    'zlwgsfd': (True, 4, lambda s, ea: (
        s(f'local val:8 = sext({mem(ea, 4)}) << 16;'), set_pair(s, 'val'))),
    'zlwwosd': (True, 4, lambda s, ea: (
        s(f'local val:8 = sext({mem(ea, 4)});'), set_pair(s, 'val'))),
    'zlwhsplatwd': (True, 4, lambda s, ea: s(
        f'local val:4 = (zext({mem(ea, 2)}) << 16) | zext({mem(ea, 2, 2)});',
        'D = val;', 'Dodd = val;')),
    'zlwhsplatd': (True, 4, lambda s, ea: s(
        f'local valh:4 = zext({mem(ea, 2)});', f'local vall:4 = zext({mem(ea, 2, 2)});',
        'D = (valh << 16) | valh;', 'Dodd = (vall << 16) | vall;')),
    'zlwhgwsfd': (True, 4, lambda s, ea: s(
        f'D = sext({mem(ea, 2)}) << 8;', f'Dodd = sext({mem(ea, 2, 2)}) << 8;')),
    'zlwhed': (True, 4, lambda s, ea: s(
        f'D = zext({mem(ea, 2)}) << 16;', f'Dodd = zext({mem(ea, 2, 2)}) << 16;')),
    'zlwhosd': (True, 4, lambda s, ea: s(
        f'D = sext({mem(ea, 2)});', f'Dodd = sext({mem(ea, 2, 2)});')),
    'zlwhoud': (True, 4, lambda s, ea: s(
        f'D = zext({mem(ea, 2)});', f'Dodd = zext({mem(ea, 2, 2)});')),
    'zlwh': (False, 4, lambda s, ea: s(
        f'D = (zext({mem(ea, 2)}) << 16) | zext({mem(ea, 2, 2)});')),
    'zlww': (False, 4, lambda s, ea: s(f'D = {mem(ea, 4)};')),
    'zlhgwsf': (False, 2, lambda s, ea: s(f'D = sext({mem(ea, 2)}) << 8;')),
    'zlhhsplat': (False, 2, lambda s, ea: s(
        f'local val:4 = zext({mem(ea, 2)});', 'D = (val << 16) | val;')),
    'zlhhe': (False, 2, lambda s, ea: s(f'D = zext({mem(ea, 2)}) << 16;')),
    'zlhhos': (False, 2, lambda s, ea: s(f'D = sext({mem(ea, 2)});')),
    'zlhhou': (False, 2, lambda s, ea: s(f'D = zext({mem(ea, 2)});')),
    'zstdd': (True, 8, lambda s, ea: s(f'{mem(ea, 8)} = (zext(D) << 32) | zext(Dodd);')),
    'zstdw': (True, 8, lambda s, ea: s(f'{mem(ea, 4)} = D;', f'{mem(ea, 4, 4)} = Dodd;')),
    'zstdh': (True, 8, lambda s, ea: s(
        f'{mem(ea, 2)} = {H("D")};', f'{mem(ea, 2, 2)} = {L("D")};',
        f'{mem(ea, 2, 4)} = {H("Dodd")};', f'{mem(ea, 2, 6)} = {L("Dodd")};')),
    'zstwhed': (True, 4, lambda s, ea: s(
        f'{mem(ea, 2)} = {H("D")};', f'{mem(ea, 2, 2)} = {H("Dodd")};')),
    'zstwhod': (True, 4, lambda s, ea: s(
        f'{mem(ea, 2)} = {L("D")};', f'{mem(ea, 2, 2)} = {L("Dodd")};')),
    'zstwh': (False, 4, lambda s, ea: s(f'{mem(ea, 2)} = {H("D")};', f'{mem(ea, 2, 2)} = {L("D")};')),
    'zstww': (False, 4, lambda s, ea: s(f'{mem(ea, 4)} = D;')),
    'zsthe': (False, 2, lambda s, ea: s(f'{mem(ea, 2)} = {H("D")};')),
    'zstho': (False, 2, lambda s, ea: s(f'{mem(ea, 2)} = {L("D")};')),
}

LDST_RE = re.compile(r'^(' + '|'.join(sorted(LOADS, key=len, reverse=True)) + r')(u|x|mx)?$')


def ldst_form(name):
    """(base, form): form is '' (d(rA)), 'u' (update), 'x' (indexed), 'mx' (modify)."""
    m = LDST_RE.match(name)
    return (m.group(1), m.group(2) or '') if m else (None, None)


# ---------------------------------------------------------------------------

FAMILIES = [
    (r'zmh(e|eo|o)g(si|ui|sui|smf)(aa|an)?', zmh_guarded),
    (r'zmh(e|eo|o)gwsmf(r?)(aa|an)?', zmh_gw),
    (r'zmh(e|eo|o)sf(r?)', zmh_sf),
    (r'zmh(e|eo|o)sf(r?)(aa|an)s', zmh_sf_acc),
    (r'zmh(e|eo|o)(s|su|u)i(aa|an)?(s?)', zmh_int),
    (r'zvmhsf(r?)h', zvmhsfh),
    (r'zvmhsf(r?)(aa|an)hs', zvmhsf_acc),
    (r'zvmh(s|su|u)i(aa|an)?h(s?)', zvmh_int_h),
    (r'zmwg(s|su|u)i(aa|an)?(s?)', zmwg_int),
    (r'zmwgsmf(r?)(aa|an)?', zmwgsmf),
    (r'zmwl(s|su|u)is', zmwl_sat),
    (r'zmwl(s|su|u)i(aa|an)(s?)', zmwl_acc),
    (r'zmwsf(r?)', zmwsf),
    (r'zmwsf(r?)(aa|an)s', zmwsf_acc),
    (r'zvmh(ul|ll|uu|xl)gwsmf(r?)(aa|an|anp)?', zvmh_gw),
    (r'zvmh(ul|ll|uu|xl)sf(r?)', zvmh_sf),
    (r'zvmh(ul|ll|uu|xl)sf(r?)(aa|an|anp)s', zvmh_sf_acc),
    (r'zvmh(ul|ll|uu|xl)(s|su|u)i(aa|an|anp)?(s?)', zvmh_int),
    (r'zvdotph(x?)g(a|s)(si|ui|sui|smf)(aa|an)?', zvdotph_g),
    (r'zvdotph(x?)(a|s)sf(r?)(aa|an)?s', zvdotph_sf),
    (r'zvdotph(x?)(a|s)(si|ui|sui)(aa|an)?(s?)', zvdotph_int),
    (r'zvdotph(x?)gw(a|s)smf(r?)(aa|an)?', zvdotph_gw),
    (r'zbrminc', zbrminc),
    (r'zcircinc', zcircinc),
    (r'zvabsh(s?)', zvabsh),
    (r'zabsw(s?)', zabsw),
    (r'(zv(?:add|subf|addsubf|subfadd)hx?)(ss|us)?', zvh_arith),
    (r'zv(add|sub)i(?:h|fh)', zvaddih),
    (r'z(add|subf)h(e|o)(s|u)w', zaddh_w),
    (r'(zv(?:add|subf|addsubf|subfadd)w)(ss|us)?', zvw_arith),
    (r'z(add|subf)w(ss|us)', zaddw_sat),
    (r'z(add|subf)wg(sf|si|ui)', zaddwg),
    (r'z(add|subf)d(ss|us)?', zaddd),
    (r'zvcmp(eqh|gths|gthu|lths|lthu)', zvcmp),
    (r'zvcntlsh|zcntlsw|zvcntlzh', zcnt),
    (r'zdivwsf', zdivwsf),
    (r'zvmerge(hih|hiloh|loh|lohih)', zvmerge),
    (r'zvnegh(o?)(s?)', zvneg),
    (r'znegws', znegws),
    (r'zvpkshgwshfrs', zvpkshgwshfrs),
    (r'zpkswg(sh|sw)frs', zpkswg),
    (r'zvpkswshfrs', zvpkswshfrs),
    (r'zvpk(s|u)w(s|u)hs', zvpk_sat),
    (r'zvrlh(i?)', zvrlh),
    (r'zrndwh(ss)?', zrndwh),
    (r'zsat(?:sdsw|sduw|uduw|swuw|uwsw|swuh|swsh|uwuh|uwsh)|zvsat(?:shuh|uhsh)', zsat),
    (r'zvselh', zvselh),
    (r'zvslh(i?)(us|ss)?', zvsl_h),
    (r'zslw(i?)(ss|us)', zslw),
    (r'zvsplat(f?)ih', zvsplat),
    (r'zvsrh(i?)(s|u)', zvsr_h),
    (r'zvunpkh(?:gwsf|sf|si|ui)|zunpkwgsf', zunpk),
    (r'zxtrw', zxtrw),
]
FAMILIES = [(re.compile(f'^(?:{pattern})$'), fn) for pattern, fn in FAMILIES]


def semantics(name):
    s = Sem()
    base, form = ldst_form(name)
    if base:
        return None
    matches = [(pattern, fn) for pattern, fn in FAMILIES if pattern.match(name)]
    if len(matches) != 1:
        raise SystemExit(f'{name}: {len(matches)} semantic families match')
    pattern, fn = matches[0]
    fn(s, pattern.match(name))
    s.spefscr()
    return s


# ---------------------------------------------------------------------------
# Constructors

def load_table():
    rows = []
    for line in TABLE.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        name, xop, b16, operands, extra = line.split('\t')
        rows.append((name, int(xop, 16), None if b16 == '-' else int(b16), operands.split(','), extra))
    return rows


SCALE = {'EVUIMM_2': 2, 'EVUIMM_4': 4, 'EVUIMM_8': 8}


def constructor(name, xop, b16, operands, extra):
    pattern = ['OP=4']
    display = []
    base, form = ldst_form(name)
    if base:
        pair, size, body = LOADS[base]
        s = Sem()
        s.pair = pair
        display.append('D')
        if form in ('', 'u'):
            scale = SCALE[operands[1].replace('_EX0', '')]
            if form == 'u':
                display.append(f'lspUpdate{scale}')
                pattern += ['D', 'A', f'lspUpdate{scale}', 'A_BITS!=0', 'EVUIMM!=0']
                s(f'local ea:4 = lspUpdate{scale};')
                body(s, 'ea')
                s('A = ea;')
            else:
                display.append(f'lspDisp{scale}')
                pattern += ['D', f'lspDisp{scale}']
                s(f'local ea:4 = lspDisp{scale};')
                body(s, 'ea')
        elif form == 'x':
            display += ['RA_OR_ZERO', 'B']
            pattern += ['D', 'RA_OR_ZERO', 'B']
            s('local ea:4 = RA_OR_ZERO + B;')
            body(s, 'ea')
        else:
            # modify: the load or store uses rB + rA[51:63], then rA[51:63] is
            # stepped by the signed offset in rA[35:40] (1.6.2)
            display += ['A', 'B']
            pattern += ['D', 'A', 'B', 'A_BITS!=0']
            s('local control:4 = A;', 'local ea:4 = (control & 0x1fff) + B;')
            body(s, 'ea')
            s('local offset:4 = (control << 3) s>> 26;')
            circular(s, 'A', 'control', 'offset')
        if s.pair != pair:
            raise SystemExit(name)
    else:
        s = semantics(name)
        ops = list(operands)
        for op in ops:
            if op in ('RD', 'RD_EVEN', 'RS', 'RS_EVEN'):
                display.append('D')
                pattern.append('D')
            elif op in ('RA', 'RB', 'CRFD'):
                display.append({'RA': 'A', 'RB': 'B', 'CRFD': 'CRFD'}[op])
                pattern.append(display[-1])
            elif op == 'EVUIMM':
                display.append('EVUIMM')
                pattern.append('EVUIMM')
            elif op == 'EVUIMM_LT16':
                display.append('EVUIMM')
                pattern += ['EVUIMM', 'BIT_15=0']
            elif op == 'SIMM':
                display.append('A_BITSS')
                pattern.append('A_BITSS')
            elif op == 'VX_OFF':
                display.append('lspOffset')
                pattern += ['lspOffset', 'BITS_0_1!=0']
            else:
                raise SystemExit(f'{name}: operand {op}')
        if extra.startswith('crf'):
            pattern.append(f'BITS_21_22={int(extra[3:], 2)}')
        if 'RS' in operands or 'RS_EVEN' in operands:
            raise SystemExit(name)
        binutils_even = 'RD_EVEN' in operands
        if binutils_even != s.pair:
            NOTES.append(f'{name}: rD pair={s.pair}, binutils RD_EVEN={binutils_even}')
    if s.pair:
        pattern += ['L2=0', 'Dodd']
    if 'VX_OFF' in operands:
        pattern.append(f'XOP_2_10={xop >> 2}')
    elif b16 is None:
        pattern.append(f'XOP_0_10={xop:#x}')
    else:
        pattern += [f'B_BITS={b16}', f'XOP_0_10={xop:#x}']
    body = '\n'.join('\t' + line if not line.startswith('<') else line for line in s.lines)
    return f':{name} {",".join(display)}\tis {" & ".join(pattern)}\n{{\n{body}\n}}\n'


NOTES = []

HEADER = '''\
# e200z4 Lightweight Signal Processing APU (LSP).
#
# Generated by tools/gen_lsp.py from tools/lsp_opcodes.txt; do not edit.
#
# Encodings and semantics: NXP "Lightweight Signal Processing APU Reference
# Manual" Rev. 3. GNU binutils 2.42 decodes zvcmpgths and zvcmplths as
# zvcmpgthu and zvcmplthu.
#
# Modelling notes:
# - Reserved encodings are not decoded: an odd rD or rS where the instruction
#   uses a register pair, rA=0 or a zero offset in the update forms, rA=0 in
#   the modify forms, and halfword shift or rotate immediates above 15.
# - SPEFSCR[OV] and SPEFSCR[SOV] are updated as described in the manual.
# - "Signed by unsigned" multiplies (su, sui) treat rA as signed and rB as
#   unsigned.
# - Leading sign bit counts include the sign bit, as for evcntlsw.
# - zbrminc uses a 16-bit mask.
# - Circular (modify) addressing: the manual's pseudo-RTL compares the biased
#   offset, which would let the index reach the buffer length; the index is
#   modelled as wrapping as soon as it passes the last byte of the buffer, as
#   the text describes. The illegal instruction exception for a mode other
#   than 0b100 in rA[32:34] and alignment exceptions are not modelled.
'''

SUBTABLES = '''\
# Odd register of the even/odd pair named by rD or rS
{odd}

# zxtrw byte offset, 1-3
lspOffset: BITS_0_1 is BITS_0_1 {{ export *[const]:8 BITS_0_1; }}

# Base + scaled immediate (1.4.1.1)
{disp}

# Base + scaled immediate with update (1.4.2): rA != 0, UIMM != 0
{update}
'''


def subtables():
    odd = '\n'.join(f'Dodd: is BITS_21_25={2 * i} {{ export r{2 * i + 1}; }}' for i in range(16))
    disp = '\n'.join(
        f'lspDisp{n}: disp^"("^RA_OR_ZERO^")" is RA_OR_ZERO & EVUIMM [ disp = EVUIMM * {n}; ] '
        f'{{ local ea:4 = RA_OR_ZERO + disp; export ea; }}' for n in (2, 4, 8))
    update = '\n'.join(
        f'lspUpdate{n}: disp^"("^A^")" is A & EVUIMM [ disp = EVUIMM * {n}; ] '
        f'{{ local ea:4 = A + disp; export ea; }}' for n in (2, 4, 8))
    return SUBTABLES.format(odd=odd, disp=disp, update=update)


def generate():
    rows = load_table()
    parts = [HEADER, subtables()]
    names = set()
    for row in rows:
        if row[0] in names:
            raise SystemExit(f'duplicate {row[0]}')
        names.add(row[0])
        parts.append(constructor(*row))
    return '\n'.join(parts)


def main():
    text = generate()
    for note in NOTES:
        print('note:', note, file=sys.stderr)
    if '--check' in sys.argv[1:]:
        if not OUT.exists() or OUT.read_text() != text:
            print(f'{OUT} is out of date; run {pathlib.Path(__file__).name}')
            sys.exit(1)
        return
    OUT.write_text(text, newline='\n')
    print(f'wrote {OUT}')


if __name__ == '__main__':
    main()
