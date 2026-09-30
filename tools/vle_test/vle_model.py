"""Independent model of the e200z4 VLE instructions tested by vle_tests.py.

Written from the Power ISA 2.06 Book VLE and EREF 2.0 descriptions, not from the SLEIGH.
Each handler gets the decoded operands (as Ghidra displays them) and the machine state, and
returns the new values of the registers it writes, the bytes it stores and the next PC.
Encodings whose result the architecture leaves undefined raise Skip.
"""
import math
import re
import struct

M32 = 0xFFFFFFFF
LT, GT, EQ, SO = 8, 4, 2, 1


class Skip(Exception):
    """The architecture leaves the result undefined, or the case is outside the model."""


def pattern(address):
    """Memory contents outside the test code; RunVleTests.pattern must agree."""
    return ((address * 0x9E3779B1) & M32) >> 24


def s32(v):
    v &= M32
    return v - (1 << 32) if v & 0x80000000 else v


def sext(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def rotl(v, n):
    n &= 31
    v &= M32
    return ((v << n) | (v >> (32 - n))) & M32 if n else v


def mask(mb, me):
    """PowerPC MASK(mb, me) with bit 0 the most significant."""
    if mb <= me:
        return sum(1 << (31 - i) for i in range(mb, me + 1))
    return M32 & ~mask(me + 1, mb - 1) if me + 1 <= mb - 1 else M32


def cr_signed(result, so):
    r = s32(result)
    return (LT if r < 0 else GT if r > 0 else EQ) | (SO if so else 0)


def compare(a, b, so):
    return (LT if a < b else GT if a > b else EQ) | (SO if so else 0)


# ---- operand parsing ----------------------------------------------------------------------

MEM_RE = re.compile(r'^(-?0x[0-9a-f]+|-?\d+)\((r\d+|0)\)$')


def num(text):
    return int(text, 0)


def reg(text):
    if not re.fullmatch(r'r\d+', text):
        raise ValueError(f'not a register: {text}')
    return int(text[1:])


def reg_or_zero(text):
    """X-form rA shown as 0 when the field is 0 and means the value 0."""
    return None if text == '0' else reg(text)


def crf(text):
    return int(text[2:])


def memop(text):
    m = MEM_RE.match(text)
    return num(m.group(1)), (None if m.group(2) == '0' else int(m.group(2)[1:]))


# ---- machine state ------------------------------------------------------------------------

def check_access(ea, size):
    """The emulator faults on an access past the end of the address space instead of
    wrapping around; such addresses are not memory on the MPC5746R anyway."""
    if ea + size > M32 + 1:
        raise Skip('access wraps past 0xffffffff')


class State:
    def __init__(self, values, address, image):
        self.gpr = values[:32]
        self.cr = values[32:40]
        self.so, self.ov, self.ca = values[40:43]
        self.lr, self.ctr = values[43:45]
        self.address = address
        self.image = image  # address -> byte of the test code

    def load(self, ea, size):
        check_access(ea, size)
        value = 0
        for i in range(size):
            a = (ea + i) & M32
            value = (value << 8) | self.image.get(a, pattern(a))
        return value


class Result:
    def __init__(self):
        self.gpr = {}
        self.cr = {}
        self.xer = {}
        self.lr = None
        self.ctr = None
        self.pc = None
        self.memory = {}

    def store(self, ea, size, value):
        check_access(ea, size)
        for i in range(size):
            self.memory[(ea + i) & M32] = (value >> (8 * (size - 1 - i))) & 0xFF


# ---- floating point -----------------------------------------------------------------------

def f32(bits):
    return struct.unpack('>f', struct.pack('>I', bits & M32))[0]


def bits(f):
    try:
        return struct.unpack('>I', struct.pack('>f', f))[0]
    except OverflowError:
        return 0x7F800000 if f > 0 else 0xFF800000


def normal(b):
    e = (b >> 23) & 0xFF
    return 0 < e < 255


def need_normal(*values):
    """EFPU2 handles zero and normal numbers; denormals, infinities and NaNs are beyond the
    IEEE p-code by design (see the README's modelling notes)."""
    for v in values:
        if not (normal(v) or v & 0x7FFFFFFF == 0):
            raise Skip('operand not zero or normal')


def fresult(x):
    b = bits(x)  # round to nearest even: the exact double result rounds correctly to single
    if not normal(b) and b & 0x7FFFFFFF:
        raise Skip('result overflow or underflow')
    return b


# ---- instruction semantics ----------------------------------------------------------------

def execute(mnemonic, operands, st, length):
    """Returns a Result, or raises Skip."""
    r = Result()
    g = st.gpr
    ops = operands.split('|') if operands else []
    nia = (st.address + length) & M32
    r.pc = nia
    base = mnemonic.rstrip('.')
    record = mnemonic.endswith('.')

    def setg(n, v):
        r.gpr[n] = v & M32

    def cr0(v):
        r.cr[0] = cr_signed(v, st.so)

    def branch(target, link=False):
        r.pc = target & M32
        if link:
            r.lr = nia

    def cond(field, name):
        c = st.cr[field]
        return {'eq': c & EQ, 'ne': not c & EQ, 'lt': c & LT, 'ge': not c & LT,
                'gt': c & GT, 'le': not c & GT, 'so': c & SO, 'ns': not c & SO}[name]

    # -- branches --
    m = re.fullmatch(r'(se|e)_b(eq|ne|lt|ge|gt|le|so|ns)(l?)', mnemonic)
    if m:
        field = crf(ops[0]) if len(ops) == 2 else 0
        target = num(ops[-1])
        if m.group(3):
            r.lr = nia
        if cond(field, m.group(2)):
            r.pc = target
        return r
    if mnemonic in ('se_b', 'e_b', 'se_bl', 'e_bl'):
        branch(num(ops[0]), mnemonic.endswith('l'))
        return r
    m = re.fullmatch(r'e_bd(n?)z(l?)', mnemonic)
    if m:
        r.ctr = (st.ctr - 1) & M32
        if m.group(2):
            r.lr = nia
        if bool(r.ctr) == bool(m.group(1)):
            r.pc = num(ops[0])
        return r
    if mnemonic in ('se_blr', 'se_blrl'):
        branch(st.lr & ~1, mnemonic == 'se_blrl')
        return r
    if mnemonic in ('se_bctr', 'se_bctrl'):
        branch(st.ctr & ~1, mnemonic == 'se_bctrl')
        return r

    # -- loads and stores --
    loads = {'lbz': (1, False), 'lhz': (2, False), 'lha': (2, True), 'lwz': (4, False)}
    stores = {'stb': 1, 'sth': 2, 'stw': 4}
    # se_ and e_ D-forms (e_...u: update), and X-forms (...x, ...ux)
    m = re.fullmatch(r'(se_|e_)?(lbz|lhz|lha|lwz|stb|sth|stw)(u?)(x?)', base)
    if m and (m.group(1) or m.group(4)):
        prefix, op, update, indexed = m.groups()
        rt = reg(ops[0])
        if indexed:
            ra = reg_or_zero(ops[1])
            ea = ((g[ra] if ra is not None else 0) + g[reg(ops[2])]) & M32
        elif prefix == 'se_':
            disp, ra = memop(ops[1])
            ea = (g[ra] + disp) & M32  # se_ forms use (RX), never 0
        else:
            disp, ra = memop(ops[1])
            ea = ((g[ra] if ra is not None else 0) + disp) & M32
        if update:
            if ra is None or (op in loads and ra == rt):
                raise Skip('invalid update form')
            setg(ra, ea)
        if op in loads:
            size, signed = loads[op]
            v = st.load(ea, size)
            setg(rt, sext(v, 8 * size) if signed else v)
        else:
            r.store(ea, stores[op], g[rt])
        return r
    if mnemonic in ('e_lmw', 'e_stmw'):
        rt = reg(ops[0])
        disp, ra = memop(ops[1])
        ea = ((g[ra] if ra is not None else 0) + disp) & M32
        if mnemonic == 'e_lmw' and ra is not None and ra >= rt:
            raise Skip('rA in the loaded range')
        for i, n in enumerate(range(rt, 32)):
            if mnemonic == 'e_lmw':
                setg(n, st.load(ea + 4 * i, 4))
            else:
                r.store(ea + 4 * i, 4, g[n])
        return r

    # -- 16-bit integer --
    if mnemonic.startswith('se_'):
        rx = reg(ops[0])
        x = g[rx]
        y = g[reg(ops[1])] if len(ops) > 1 and ops[1].startswith('r') else None
        imm = num(ops[1]) if len(ops) > 1 and not ops[1].startswith('r') else None
        if base == 'se_add':
            setg(rx, x + y)
        elif base == 'se_addi':
            setg(rx, x + imm)
        elif base == 'se_and':
            setg(rx, x & y)
            if record:
                cr0(x & y)
        elif base == 'se_andc':
            setg(rx, x & ~y)
        elif base == 'se_andi':
            setg(rx, x & imm)
        elif base == 'se_or':
            setg(rx, x | y)
        elif base == 'se_sub':
            setg(rx, x - y)
        elif base == 'se_subf':
            setg(rx, y - x)
        elif base == 'se_subi':
            setg(rx, x - imm)
            if record:
                cr0(x - imm)
        elif base == 'se_mullw':
            setg(rx, x * y)
        elif base == 'se_neg':
            setg(rx, -x)
        elif base == 'se_not':
            setg(rx, ~x)
        elif base == 'se_mr':
            setg(rx, y)
        elif base in ('se_mfar', 'se_mtar'):
            setg(rx, y)
        elif base == 'se_li':
            setg(rx, imm)
        elif base == 'se_bclri':
            setg(rx, x & ~(0x80000000 >> imm))
        elif base == 'se_bseti':
            setg(rx, x | (0x80000000 >> imm))
        elif base == 'se_bgeni':
            setg(rx, 0x80000000 >> imm)
        elif base == 'se_bmaski':
            setg(rx, M32 if imm == 0 else (1 << imm) - 1)
        elif base == 'se_btsti':
            r.cr[0] = (GT if x & (0x80000000 >> imm) else EQ) | (SO if st.so else 0)
        elif base == 'se_cmp':
            r.cr[0] = compare(s32(x), s32(y), st.so)
        elif base == 'se_cmpl':
            r.cr[0] = compare(x, y, st.so)
        elif base == 'se_cmpi':
            r.cr[0] = compare(s32(x), imm, st.so)
        elif base == 'se_cmpli':
            r.cr[0] = compare(x, imm, st.so)
        elif base == 'se_extsb':
            setg(rx, sext(x, 8))
        elif base == 'se_extsh':
            setg(rx, sext(x, 16))
        elif base == 'se_extzb':
            setg(rx, x & 0xFF)
        elif base == 'se_extzh':
            setg(rx, x & 0xFFFF)
        elif base == 'se_slwi':
            setg(rx, x << imm)
        elif base == 'se_srwi':
            setg(rx, x >> imm)
        elif base == 'se_srawi':
            setg(rx, s32(x) >> imm)
            r.xer['ca'] = int(s32(x) < 0 and (x & ((1 << imm) - 1)) != 0)
        elif base in ('se_slw', 'se_srw', 'se_sraw'):
            n = y & 0x3F
            if base == 'se_slw':
                setg(rx, 0 if n > 31 else x << n)
            elif base == 'se_srw':
                setg(rx, 0 if n > 31 else x >> n)
            else:
                setg(rx, s32(x) >> min(n, 31))
                r.xer['ca'] = int(s32(x) < 0 and (x & ((1 << min(n, 32)) - 1) & M32) != 0)
        elif base == 'se_mfctr':
            setg(rx, st.ctr)
        elif base == 'se_mflr':
            setg(rx, st.lr)
        elif base == 'se_mtctr':
            r.ctr = x
        elif base == 'se_mtlr':
            r.lr = x
        else:
            raise KeyError(mnemonic)
        return r

    # -- 32-bit VLE integer --
    if mnemonic.startswith('e_'):
        if base in ('e_add16i', 'e_addi', 'e_mulli', 'e_subfic'):
            rd, ra, imm = reg(ops[0]), reg(ops[1]), num(ops[2])
            a = g[ra]
            if base == 'e_add16i':
                v = a + imm
            elif base == 'e_addi':
                v = a + imm
            elif base == 'e_mulli':
                v = s32(a) * s32(imm)
            else:
                v = imm - a
                r.xer['ca'] = int((~a & M32) + (imm & M32) + 1 > M32)
            setg(rd, v)
            if record:
                cr0(v)
        elif base in ('e_add2is', 'e_or2i', 'e_or2is', 'e_and2i', 'e_and2is', 'e_li', 'e_lis',
                      'e_cmp16i', 'e_cmpl16i'):
            rd, imm = reg(ops[0]), num(ops[1])
            d = g[rd]
            if base == 'e_add2is':
                setg(rd, d + (imm << 16))
            elif base == 'e_or2i':
                setg(rd, d | (imm & 0xFFFF))
            elif base == 'e_or2is':
                setg(rd, d | ((imm & 0xFFFF) << 16))
            elif base == 'e_and2i':
                setg(rd, d & (imm & 0xFFFF))
                cr0(d & (imm & 0xFFFF))
            elif base == 'e_and2is':
                setg(rd, d & ((imm & 0xFFFF) << 16))
                cr0(d & ((imm & 0xFFFF) << 16))
            elif base == 'e_li':
                setg(rd, imm)
            elif base == 'e_lis':
                setg(rd, imm << 16)
            elif base == 'e_cmp16i':
                r.cr[0] = compare(s32(d), s32(imm), st.so)
            else:
                r.cr[0] = compare(d, imm & M32, st.so)
        elif base in ('e_andi', 'e_ori', 'e_xori'):
            ra, rs, imm = reg(ops[0]), reg(ops[1]), num(ops[2]) & M32
            s = g[rs]
            v = {'e_andi': s & imm, 'e_ori': s | imm, 'e_xori': s ^ imm}[base]
            setg(ra, v)
            if record:
                cr0(v)
        elif base in ('e_cmpi', 'e_cmpli'):
            field, ra, imm = crf(ops[0]), reg(ops[1]), num(ops[2])
            if base == 'e_cmpi':
                r.cr[field] = compare(s32(g[ra]), s32(imm), st.so)
            else:
                r.cr[field] = compare(g[ra], imm & M32, st.so)
        elif base in ('e_rlwinm', 'e_rlwimi'):
            ra, rs, sh, mb, me = reg(ops[0]), reg(ops[1]), num(ops[2]), num(ops[3]), num(ops[4])
            rot, m = rotl(g[rs], sh), mask(mb, me)
            setg(ra, rot & m if base == 'e_rlwinm' else (rot & m) | (g[ra] & ~m))
        elif base == 'e_rlw':
            ra, rs, rb = reg(ops[0]), reg(ops[1]), reg(ops[2])
            setg(ra, rotl(g[rs], g[rb] & 31))
        elif base in ('e_slwi', 'e_srwi'):
            ra, rs, sh = reg(ops[0]), reg(ops[1]), num(ops[2])
            v = g[rs] << sh if base == 'e_slwi' else g[rs] >> sh
            setg(ra, v)
            if record:
                cr0(v)
        elif base in ('e_addbus', 'e_addhus', 'e_addwus', 'e_addwss', 'e_subfbus', 'e_subfhus'):
            rd, a, b = reg(ops[0]), g[reg(ops[1])], g[reg(ops[2])]
            width = {'b': 8, 'h': 16, 'w': 32}[base[-3]]
            top = (1 << width) - 1
            a, b = a & top, b & top
            if base == 'e_addwss':
                v = max(-(1 << 31), min((1 << 31) - 1, s32(a) + s32(b)))
            elif base.startswith('e_add'):
                v = min(top, a + b)
            else:
                v = max(0, b - a)
            setg(rd, v)
        else:
            raise KeyError(mnemonic)
        return r

    # -- EFPU2 --
    if mnemonic.startswith('efs'):
        rd = crf(ops[0]) if mnemonic.startswith('efstst') else reg(ops[0])
        a = g[reg(ops[1])]
        b = g[reg(ops[2])] if len(ops) > 2 else None
        if base in ('efsabs', 'efsneg'):
            if (a >> 23) & 0xFF == 0xFF and a & 0x7FFFFF:
                raise Skip('NaN: the p-code float operations do not keep the payload')
            setg(rd, a & 0x7FFFFFFF if base == 'efsabs' else a ^ 0x80000000)
        elif base in ('efsadd', 'efssub', 'efsmul', 'efsdiv'):
            need_normal(a, b)
            x, y = f32(a), f32(b)
            if base == 'efsdiv' and y == 0:
                raise Skip('divide by zero')
            v = {'efsadd': x + y, 'efssub': x - y, 'efsmul': x * y,
                 'efsdiv': x / y if y else 0}[base]
            setg(rd, fresult(v))
        elif base in ('efsmadd', 'efsmsub', 'efsnmsub'):
            c = g[rd]
            need_normal(a, b, c)
            # the p-code rounds the product and then the sum (README: rounds twice)
            p = f32(fresult(f32(a) * f32(b)))
            v = {'efsmadd': p + f32(c), 'efsmsub': p - f32(c), 'efsnmsub': -(p - f32(c))}[base]
            setg(rd, fresult(v))
        elif base in ('efsmax', 'efsmin'):
            need_normal(a, b)
            x, y = f32(a), f32(b)
            if x == y:
                raise Skip('equal values: sign of zero')
            setg(rd, a if (x > y) == (base == 'efsmax') else b)
        elif base in ('efscfsi', 'efscfui'):
            v = s32(a) if base == 'efscfsi' else a
            setg(rd, bits(float(v)))
        elif base in ('efsctsiz', 'efsctuiz', 'efsctui'):
            need_normal(a)
            x = f32(a)
            if base == 'efsctsiz':
                if not -2**31 <= math.trunc(x) < 2**31:
                    raise Skip('out of range: not saturated (README)')
                setg(rd, math.trunc(x))
            else:
                if base == 'efsctui' and x - math.floor(x) == 0.5:
                    raise Skip('halfway: the p-code rounds up, not to even (README)')
                v = math.trunc(x) if base == 'efsctuiz' else round(x)  # round half to even
                if not 0 <= v <= M32:
                    raise Skip('out of range: not saturated (README)')
                setg(rd, v)
        elif base.startswith('efstst'):
            need_normal(a, b)
            x, y = f32(a), f32(b)
            hit = {'efststeq': x == y, 'efststgt': x > y, 'efststlt': x < y}[base]
            r.cr[rd] = ('gt-only', GT if hit else 0)
        else:
            raise KeyError(mnemonic)
        return r

    # -- 32-bit X-form integer --
    d = reg(ops[0]) if ops and ops[0].startswith('r') else None
    if base in ('add', 'subf', 'divw', 'divwu', 'mullw'):
        a, b = g[reg(ops[1])], g[reg(ops[2])]
        if base == 'add':
            v = a + b
        elif base == 'subf':
            v = b - a
        elif base == 'mullw':
            v = s32(a) * s32(b)
        elif base == 'divw':
            if b == 0 or (a == 0x80000000 and b == M32):
                raise Skip('undefined quotient')
            q = abs(s32(a)) // abs(s32(b))
            v = q if (s32(a) < 0) == (s32(b) < 0) else -q
        else:
            if b == 0:
                raise Skip('undefined quotient')
            v = a // b
        setg(d, v)
        if record:
            cr0(v)
    elif base in ('addze', 'neg'):
        a = g[reg(ops[1])]
        if base == 'addze':
            v = a + st.ca
            r.xer['ca'] = int(v > M32)
        else:
            v = -a
        setg(d, v)
        if record:
            cr0(v)
    elif base in ('and', 'andc', 'or', 'orc', 'nor', 'xor', 'eqv', 'slw', 'srw', 'sraw'):
        s, b = g[reg(ops[1])], g[reg(ops[2])]
        if base in ('slw', 'srw', 'sraw'):
            n = b & 0x3F
            if base == 'slw':
                v = 0 if n > 31 else s << n
            elif base == 'srw':
                v = 0 if n > 31 else s >> n
            else:
                v = s32(s) >> min(n, 31)
                r.xer['ca'] = int(s32(s) < 0 and (s & ((1 << min(n, 32)) - 1) & M32) != 0)
        else:
            v = {'and': s & b, 'andc': s & ~b, 'or': s | b, 'orc': s | ~b, 'nor': ~(s | b),
                 'xor': s ^ b, 'eqv': ~(s ^ b)}[base]
        setg(d, v)
        if record:
            cr0(v & M32)
    elif base == 'srawi':
        s, n = g[reg(ops[1])], num(ops[2])
        setg(d, s32(s) >> n)
        r.xer['ca'] = int(s32(s) < 0 and (s & ((1 << n) - 1)) != 0)
    elif base in ('extsb', 'extsh', 'cntlzw'):
        s = g[reg(ops[1])]
        if base == 'cntlzw':
            v = 32 - s.bit_length()
        else:
            v = sext(s, 8 if base == 'extsb' else 16)
        setg(d, v)
        if record:
            cr0(v & M32)
    elif base in ('cmpw', 'cmplw'):
        if not ops[0].startswith('cr'):
            ops = ['cr0'] + ops  # cr0 is not displayed
        field, a, b = crf(ops[0]), g[reg(ops[1])], g[reg(ops[2])]
        r.cr[field] = compare(s32(a), s32(b), st.so) if base == 'cmpw' else compare(a, b, st.so)
    elif base.startswith('isel'):
        ra = reg_or_zero(ops[1])
        a = g[ra] if ra is not None else 0
        field = crf(ops[3])
        setg(d, a if cond(field, base[4:]) else g[reg(ops[2])])
    elif base == 'mfcr':
        setg(d, sum(st.cr[i] << (4 * (7 - i)) for i in range(8)))
    elif base == 'mtcrf':
        fxm, s = num(ops[0]), g[reg(ops[1])]
        for i in range(8):
            if fxm & (0x80 >> i):
                r.cr[i] = (s >> (4 * (7 - i))) & 0xF
    else:
        raise KeyError(mnemonic)
    return r
