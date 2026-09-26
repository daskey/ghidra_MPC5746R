"""Reference model of the e200z4 LSP APU, written directly from the pseudo-RTL
of the NXP LSP APU Reference Manual Rev. 3 (section 1.6). Bits are numbered
big-endian as in the manual: bit 0 is the most significant bit of a field.

This is deliberately independent of tools/gen_lsp.py: it follows the RTL
step by step with explicit bit widths instead of wide arithmetic."""
import re

M32 = 0xffffffff


def mask(n):
    return (1 << n) - 1


def bit(v, i, w):
    """Bit i (0 = msb) of the w-bit value v."""
    return (v >> (w - 1 - i)) & 1


def fld(v, i, j, w):
    """Bits i..j (0 = msb) of the w-bit value v."""
    return (v >> (w - 1 - j)) & mask(j - i + 1)


def exts(v, n, w):
    v &= mask(n)
    if v >> (n - 1):
        v |= mask(w) ^ mask(n)
    return v


def extz(v, n, w):
    return v & mask(n)


def ext(v, n, w, ty):
    return extz(v, n, w) if ty == 0 else exts(v, n, w)


def sval(v, n):
    v &= mask(n)
    return v - (1 << n) if v >> (n - 1) else v


def ROUND(v, bits, w):
    return (((1 << (bits - 1)) + v) & (mask(w) ^ mask(bits))) & mask(w)


def chk_ovf(v, n):
    v &= mask(n)
    return 0 if v in (0, mask(n)) else 1


def chk_ovfu(v, n):
    return 0 if v & mask(n) == 0 else 1


def SATURATE(ov, carry, under, over, value):
    if ov:
        return under if carry else over
    return value


def BITREVERSE(v):
    r = 0
    for i in range(32):
        if v & (1 << i):
            r |= 1 << (31 - i)
    return r


def H0(r):
    return fld(r, 0, 15, 32)


def H1(r):
    return fld(r, 16, 31, 32)


def join(h, l):
    return ((h & 0xffff) << 16) | (l & 0xffff)


def mul(a, b, n, ty):
    """a TY b for n-bit operands: 2n-bit result. TY 0 ui, 1 si, 2 sui, 3 sf."""
    if ty == 0:
        p = a * b
    elif ty == 1:
        p = sval(a, n) * sval(b, n)
    elif ty == 2:
        p = sval(a, n) * (b & mask(n))
    else:
        p = (sval(a, n) * sval(b, n)) << 1
    return p & mask(2 * n)


class State:
    def __init__(self, regs, cr, spefscr, mem):
        self.r = list(regs)
        self.cr = list(cr)          # 8 fields, 4 bits each, cr0 first
        self.spefscr = spefscr
        self.mem = mem              # bytearray, address = index
        self.written = {}

    def rd(self, addr, n):
        v = 0
        for i in range(n):
            a = (addr + i) & M32
            v = (v << 8) | self.written.get(a, self.mem[a] if a < len(self.mem) else 0)
        return v

    def wr(self, addr, n, v):
        for i in range(n):
            self.written[(addr + i) & M32] = (v >> (8 * (n - 1 - i))) & 0xff

    def ov(self, ov):
        # SPEFSCR[OV] (bit 49) = ov, SPEFSCR[SOV] (bit 48) |= ov
        self.spefscr = (self.spefscr & ~0x4000) | (0x4000 if ov else 0) | (0x8000 if ov else 0)


# ---------------------------------------------------------------------------

class Insn:
    def __init__(self, st, word):
        self.st = st
        self.w = word
        self.rD = (word >> 21) & 31
        self.rA = (word >> 16) & 31
        self.rB = (word >> 11) & 31
        self.uimm = self.rB
        self.crfD = (word >> 23) & 7

    @property
    def D(self):
        return self.st.r[self.rD]

    @property
    def D1(self):
        return self.st.r[self.rD + 1]

    @property
    def A(self):
        return self.st.r[self.rA]

    @property
    def B(self):
        return self.st.r[self.rB]

    def setD(self, v):
        self.st.r[self.rD] = v & M32

    def setD1(self, v):
        self.st.r[self.rD + 1] = v & M32

    def setA(self, v):
        self.st.r[self.rA] = v & M32

    def pair(self):
        return (self.D << 32) | self.D1

    def setpair(self, v):
        self.setD(v >> 32)
        self.setD1(v)


SIMPLE = {}


def simple(*names):
    def deco(fn):
        for n in names:
            SIMPLE[n] = fn
        return fn
    return deco


@simple('zbrminc')
def _(i, n):
    Mask = i.B & 0xffff          # MASKBITS = 16
    a = i.A & 0xffff
    d = BITREVERSE((1 + BITREVERSE((a | (~Mask & M32)) & M32)) & M32)
    i.setD(join(H0(i.A), (a & ~Mask) | (d & Mask)))


def circinc(index, offset_biased, length):
    """Index + actual offset, wrapping within the buffer of (length+1)*8 bytes."""
    last = (length << 3) | 7
    actual = offset_biased + 1 if offset_biased >= 0 else offset_biased
    new = index + actual
    if new > last:
        new -= last + 1
    elif new < 0:
        new += last + 1
    return new & 0x1fff


@simple('zcircinc')
def _(i, n):
    offset = sval(i.B & 0x3fff, 14)                 # rB[50:63]
    length = fld(i.A, 41 - 32, 50 - 32, 32)          # rA[41:50]
    index = fld(i.A, 51 - 32, 63 - 32, 32)           # rA[51:63]
    i.setD((i.A & ~0x1fff) | circinc(index, offset, length))


@simple('zvabsh', 'zvabshs')
def _(i, n):
    ov = 0
    out = []
    for h in (H0(i.A), H1(i.A)):
        if n == 'zvabshs' and h == 0x8000:
            out.append(0x7fff)
            ov = 1
        else:
            out.append(abs(sval(h, 16)) & 0xffff)
    i.setD(join(*out))
    if n == 'zvabshs':
        i.st.ov(ov)


@simple('zabsw', 'zabsws')
def _(i, n):
    if n == 'zabsws' and i.A == 0x80000000:
        i.setD(0x7fffffff)
        i.st.ov(1)
        return
    i.setD(abs(sval(i.A, 32)))
    if n == 'zabsws':
        i.st.ov(0)


@simple('zaddd', 'zsubfd')
def _(i, n):
    ab = (i.A << 32) | i.B
    i.setpair(i.pair() + ab if n == 'zaddd' else i.pair() - ab)


@simple('zadddss', 'zsubfdss')
def _(i, n):
    ab = (i.A << 32) | i.B
    if n == 'zadddss':
        temp = (exts(ab, 64, 65) + exts(i.pair(), 64, 65)) & mask(65)
    else:
        temp = (exts(i.pair(), 64, 65) - exts(ab, 64, 65)) & mask(65)
    ov = bit(temp, 0, 65) ^ bit(temp, 1, 65)
    i.setpair(SATURATE(ov, bit(temp, 0, 65), 0x8000000000000000, 0x7fffffffffffffff,
                       fld(temp, 1, 64, 65)))
    i.st.ov(ov)


@simple('zadddus', 'zsubfdus')
def _(i, n):
    ab = (i.A << 32) | i.B
    if n == 'zadddus':
        temp = (ab + i.pair()) & mask(65)
        ov = bit(temp, 0, 65)
        i.setpair(SATURATE(ov, 1, 0xffffffffffffffff, None, fld(temp, 1, 64, 65)))
    else:
        temp = (i.pair() - ab) & mask(65)
        ov = bit(temp, 0, 65)
        i.setpair(SATURATE(ov, 1, 0, None, fld(temp, 1, 64, 65)))
    i.st.ov(ov)


def hsat(temp, signed):
    """RTL for halfword add/sub with saturation from a 32-bit temp."""
    if signed:
        ov = bit(temp, 15, 32) ^ bit(temp, 16, 32)
        return SATURATE(ov, bit(temp, 15, 32), 0x8000, 0x7fff, fld(temp, 16, 31, 32)), ov
    ov = bit(temp, 15, 32)
    return ov, ov


# (h op, l op, exchanged)
VH = {'zvaddh': ('+', '+', 0), 'zvsubfh': ('-', '-', 0), 'zvaddsubfh': ('+', '-', 0),
      'zvsubfaddh': ('-', '+', 0), 'zvaddhx': ('+', '+', 1), 'zvsubfhx': ('-', '-', 1),
      'zvaddsubfhx': ('+', '-', 1), 'zvsubfaddhx': ('-', '+', 1)}


def vh(i, n):
    m = re.match(r'^(zv(?:add|subf|addsubf|subfadd)hx?)(ss|us)?$', n)
    base, sat = m.groups()
    oph, opl, x = VH[base]
    ah, al = (H1(i.A), H0(i.A)) if x else (H0(i.A), H1(i.A))
    out, ovs = [], 0
    for b, a, op in ((H0(i.B), ah, oph), (H1(i.B), al, opl)):
        if not sat:
            out.append((b + a if op == '+' else b - a) & 0xffff)
            continue
        if sat == 'ss':
            temp = (exts(b, 16, 32) + exts(a, 16, 32) if op == '+'
                    else exts(b, 16, 32) - exts(a, 16, 32)) & M32
            ov = bit(temp, 15, 32) ^ bit(temp, 16, 32)
            out.append(SATURATE(ov, bit(temp, 15, 32), 0x8000, 0x7fff, fld(temp, 16, 31, 32)))
        else:
            temp = (b + a if op == '+' else b - a) & M32
            ov = bit(temp, 15, 32)
            out.append(SATURATE(ov, 1, 0xffff if op == '+' else 0, None, fld(temp, 16, 31, 32)))
        ovs |= ov
    i.setD(join(*out))
    if sat:
        i.st.ov(ovs)


for _n in VH:
    for _s in ('', 'ss', 'us'):
        SIMPLE[_n + _s] = vh


@simple('zvaddih', 'zvsubifh')
def _(i, n):
    u = i.uimm
    if n == 'zvaddih':
        i.setD(join(H0(i.A) + u, H1(i.A) + u))
    else:
        i.setD(join(H0(i.A) - u, H1(i.A) - u))


@simple('zaddhesw', 'zaddheuw', 'zaddhosw', 'zaddhouw',
        'zsubfhesw', 'zsubfheuw', 'zsubfhosw', 'zsubfhouw')
def _(i, n):
    m = re.match(r'^z(add|subf)h(e|o)(s|u)w$', n)
    op, eo, su = m.groups()
    g = H0 if eo == 'e' else H1
    e = (lambda v: exts(v, 16, 32)) if su == 's' else (lambda v: v)
    i.setD(e(g(i.B)) + e(g(i.A)) if op == 'add' else e(g(i.B)) - e(g(i.A)))


VW = {'zvaddw': ('+', '+'), 'zvsubfw': ('-', '-'), 'zvaddsubfw': ('+', '-'),
      'zvsubfaddw': ('-', '+')}


def vw(i, n):
    m = re.match(r'^(zv(?:add|subf|addsubf|subfadd)w)(ss|us)?$', n)
    base, sat = m.groups()
    oph, opl = VW[base]
    res, ovs = [], 0
    for acc, src, op in ((i.D, i.A, oph), (i.D1, i.B, opl)):
        if not sat:
            res.append(acc + src if op == '+' else acc - src)
            continue
        if sat == 'ss':
            temp = (exts(acc, 32, 33) + exts(src, 32, 33) if op == '+'
                    else exts(acc, 32, 33) - exts(src, 32, 33)) & mask(33)
            ov = bit(temp, 0, 33) ^ bit(temp, 1, 33)
            res.append(SATURATE(ov, bit(temp, 0, 33), 0x80000000, 0x7fffffff, fld(temp, 1, 32, 33)))
        else:
            temp = (acc + src if op == '+' else acc - src) & mask(33)
            ov = bit(temp, 0, 33)
            res.append(SATURATE(ov, 1, 0xffffffff if op == '+' else 0, None, fld(temp, 1, 32, 33)))
        ovs |= ov
    i.setD(res[0])
    i.setD1(res[1])
    if sat:
        i.st.ov(ovs)


for _n in VW:
    for _s in ('', 'ss', 'us'):
        SIMPLE[_n + _s] = vw


@simple('zaddwgsf', 'zaddwgsi', 'zaddwgui', 'zsubfwgsf', 'zsubfwgsi', 'zsubfwgui')
def _(i, n):
    m = re.match(r'^z(add|subf)wg(sf|si|ui)$', n)
    op, ty = m.groups()
    if ty == 'sf':
        a, b = exts(i.A, 32, 48) << 16, exts(i.B, 32, 48) << 16
    elif ty == 'si':
        a, b = exts(i.A, 32, 64), exts(i.B, 32, 64)
    else:
        a, b = i.A, i.B
    i.setpair((b + a if op == 'add' else b - a) & mask(64))


@simple('zaddwss', 'zsubfwss', 'zaddwus', 'zsubfwus')
def _(i, n):
    m = re.match(r'^z(add|subf)w(ss|us)$', n)
    op, sat = m.groups()
    if sat == 'ss':
        temp = (exts(i.B, 32, 33) + exts(i.A, 32, 33) if op == 'add'
                else exts(i.B, 32, 33) - exts(i.A, 32, 33)) & mask(33)
        ov = bit(temp, 0, 33) ^ bit(temp, 1, 33)
        i.setD(SATURATE(ov, bit(temp, 0, 33), 0x80000000, 0x7fffffff, fld(temp, 1, 32, 33)))
    else:
        temp = (i.B + i.A if op == 'add' else i.B - i.A) & mask(33)
        ov = bit(temp, 0, 33)
        i.setD(SATURATE(ov, 1, 0xffffffff if op == 'add' else 0, None, fld(temp, 1, 32, 33)))
    i.st.ov(ov)


@simple('zvcmpeqh', 'zvcmpgths', 'zvcmpgthu', 'zvcmplths', 'zvcmplthu')
def _(i, n):
    kind = n[5:]
    def cmp(a, b):
        if kind == 'eqh':
            return a == b
        if kind[-1] == 's':
            a, b = sval(a, 16), sval(b, 16)
        return a > b if kind.startswith('gt') else a < b
    ch = int(cmp(H0(i.A), H0(i.B)))
    cl = int(cmp(H1(i.A), H1(i.B)))
    i.st.cr[i.crfD] = (ch << 3) | (cl << 2) | ((ch | cl) << 1) | (ch & cl)


def cntls(v, n):
    s = v >> (n - 1)
    c = 0
    for k in range(n - 1, -1, -1):
        if (v >> k) & 1 != s:
            break
        c += 1
    return c


def cntlz(v, n):
    c = 0
    for k in range(n - 1, -1, -1):
        if (v >> k) & 1:
            break
        c += 1
    return c


@simple('zvcntlsh', 'zcntlsw', 'zvcntlzh')
def _(i, n):
    if n == 'zcntlsw':
        i.setD(cntls(i.A, 32))
    elif n == 'zvcntlsh':
        i.setD(join(cntls(H0(i.A), 16), cntls(H1(i.A), 16)))
    else:
        i.setD(join(cntlz(H0(i.A), 16), cntlz(H1(i.A), 16)))


@simple('zdivwsf')
def _(i, n):
    dividend, divisor = sval(i.A, 32), sval(i.B, 32)
    ov = 0
    if bit(i.A, 0, 32) ^ bit(i.B, 0, 32) and (abs(dividend) > abs(divisor) or divisor == 0):
        i.setD(0x80000000)
        ov = 1
    elif not (bit(i.A, 0, 32) ^ bit(i.B, 0, 32)) and (abs(dividend) >= abs(divisor) or divisor == 0):
        i.setD(0x7fffffff)
        ov = 1
    else:
        # dividend = quotient xsf divisor + remainder, remainder has the dividend's sign
        num = dividend << 31
        q = abs(num) // abs(divisor)
        if (num < 0) != (divisor < 0):
            q = -q
        i.setD(q)
    i.st.ov(ov)


@simple('zvmergehih', 'zvmergehiloh', 'zvmergeloh', 'zvmergelohih')
def _(i, n):
    sel = {'hih': (H0, H0), 'hiloh': (H0, H1), 'loh': (H1, H1), 'lohih': (H1, H0)}[n[7:]]
    i.setD(join(sel[0](i.A), sel[1](i.B)))


@simple('zvnegh', 'zvnegho', 'zvneghos', 'zvneghs')
def _(i, n):
    h, l = H0(i.A), H1(i.A)
    ov = 0
    if n in ('zvnegh', 'zvneghs'):
        if n == 'zvneghs' and h == 0x8000:
            h, ov = 0x7fff, 1
        else:
            h = -h
    if n == 'zvneghs' or n == 'zvneghos':
        if l == 0x8000:
            l, ov = 0x7fff, 1
        else:
            l = -l
    else:
        l = -l
    i.setD(join(h, l))
    if n in ('zvneghs', 'zvneghos'):
        i.st.ov(ov)


@simple('znegws')
def _(i, n):
    if i.A == 0x80000000:
        i.setD(0x7fffffff)
        i.st.ov(1)
    else:
        i.setD(-i.A)
        i.st.ov(0)


@simple('zvpkshgwshfrs')
def _(i, n):
    out, ovs = [], 0
    for x in (i.A, i.B):
        if sval(x, 32) >= 0x007fff80 or sval(x, 32) < sval(0xff7fff80, 32):
            ov = 1
            temp = SATURATE(ov, bit(x, 0, 32), 0x00800000, 0x007fffff, None)
        else:
            ov = 0
            temp = ROUND(x, 8, 32)
        out.append(fld(temp, 8, 23, 32))
        ovs |= ov
    i.setD(join(*out))
    i.st.ov(ovs)


@simple('zpkswgshfrs')
def _(i, n):
    v = (i.A << 32) | i.B
    if sval(v, 64) < sval(0xffff7fff80000000, 64) or sval(v, 64) >= 0x00007fff80000000:
        ov = 1
        templ = SATURATE(ov, bit(i.A, 0, 32), 0x8000, 0x7fff, None)
    else:
        ov = 0
        tempr = ROUND(v, 32, 64)
        templ = fld(tempr, 16, 31, 64)
    i.setD(templ << 16)
    i.st.ov(ov)


@simple('zpkswgswfrs')
def _(i, n):
    v = (i.A << 32) | i.B
    if sval(v, 64) < sval(0xffff7fffffff8000, 64) or sval(v, 64) >= 0x00007fffffff8000:
        ov = 1
        templ = SATURATE(ov, bit(i.A, 0, 32), 0x80000000, 0x7fffffff, None)
    else:
        ov = 0
        tempr = ROUND(v, 16, 64)
        templ = fld(tempr, 16, 47, 64)
    i.setD(templ)
    i.st.ov(ov)


@simple('zvpkswshfrs')
def _(i, n):
    out, ovs = [], 0
    for x in (i.A, i.B):
        if sval(x, 32) >= 0x7fff8000:
            ov, t = 1, 0x7fff
        else:
            ov = 0
            tempr = ROUND(exts(x, 32, 64), 16, 64)
            t = fld(tempr, 32, 47, 64)
        out.append(t)
        ovs |= ov
    i.setD(join(*out))
    i.st.ov(ovs)


@simple('zvpkswshs', 'zvpkswuhs', 'zvpkuwuhs')
def _(i, n):
    out, ovs = [], 0
    for x in (i.A, i.B):
        if n == 'zvpkswshs':
            ov = int(sval(x, 32) < -0x8000 or sval(x, 32) > 0x7fff)
            out.append(SATURATE(ov, bit(x, 0, 32), 0x8000, 0x7fff, x & 0xffff))
        elif n == 'zvpkswuhs':
            ov = int(sval(x, 32) < 0 or sval(x, 32) > 0xffff)
            out.append(SATURATE(ov, bit(x, 0, 32), 0x0000, 0xffff, x & 0xffff))
        else:
            ov = int(x > 0xffff)
            out.append(SATURATE(ov, 0, None, 0xffff, x & 0xffff))
        ovs |= ov
    i.setD(join(*out))
    i.st.ov(ovs)


def rotl16(v, n):
    n %= 16
    return ((v << n) | (v >> (16 - n))) & 0xffff


@simple('zvrlh', 'zvrlhi')
def _(i, n):
    if n == 'zvrlhi':
        nh = nl = i.uimm
    else:
        nh, nl = fld(i.B, 44 - 32, 47 - 32, 32), fld(i.B, 60 - 32, 63 - 32, 32)
    i.setD(join(rotl16(H0(i.A), nh), rotl16(H1(i.A), nl)))


@simple('zrndwh')
def _(i, n):
    i.setD((i.A + 0x8000) & 0xffff0000)


@simple('zrndwhss')
def _(i, n):
    if sval(i.A, 32) >= 0x7fff8000:
        templ, ov = 0x7fff0000, 1
    else:
        templ, ov = i.A + 0x8000, 0
    i.setD(templ & 0xffff0000)
    i.st.ov(ov)


@simple('zsatsdsw')
def _(i, n):
    t = sval((i.A << 32) | i.B, 64)
    ov = int(t < -0x80000000 or t > 0x7fffffff)
    i.setD(SATURATE(ov, bit(i.A, 0, 32), 0x80000000, 0x7fffffff, i.B))
    i.st.ov(ov)


@simple('zsatsduw')
def _(i, n):
    t = sval((i.A << 32) | i.B, 64)
    ov = int(t < 0 or t > 0xffffffff)
    i.setD(SATURATE(ov, bit(i.A, 0, 32), 0, 0xffffffff, i.B))
    i.st.ov(ov)


@simple('zsatuduw')
def _(i, n):
    ov = int(i.A != 0)
    i.setD(SATURATE(ov, 0, None, 0xffffffff, i.B))
    i.st.ov(ov)


@simple('zvsatshuh')
def _(i, n):
    out, ovs = [], 0
    for h in (H0(i.A), H1(i.A)):
        ov = int(sval(h, 16) < 0)
        out.append(SATURATE(ov, 0, None, 0x0000, h))
        ovs |= ov
    i.setD(join(*out))
    i.st.ov(ovs)


@simple('zvsatuhsh')
def _(i, n):
    out, ovs = [], 0
    for h in (H0(i.A), H1(i.A)):
        ov = int(h > 0x7fff)
        out.append(SATURATE(ov, 0, None, 0x7fff, h))
        ovs |= ov
    i.setD(join(*out))
    i.st.ov(ovs)


@simple('zsatswsh', 'zsatswuh', 'zsatswuw', 'zsatuwsw', 'zsatuwsh', 'zsatuwuh')
def _(i, n):
    a = i.A
    s = sval(a, 32)
    if n == 'zsatswsh':
        ov = int(s < -0x8000 or s > 0x7fff)
        r = SATURATE(ov, bit(a, 0, 32), 0xffff8000, 0x00007fff, a)
    elif n == 'zsatswuh':
        ov = int(s < 0 or s > 0xffff)
        r = SATURATE(ov, bit(a, 0, 32), 0x0000, 0xffff, a & 0xffff)
    elif n == 'zsatswuw':
        ov = int(s < 0)
        r = SATURATE(ov, 0, None, 0x00000000, a)
    elif n == 'zsatuwsw':
        ov = int(a > 0x7fffffff)
        r = SATURATE(ov, 0, None, 0x7fffffff, a)
    elif n == 'zsatuwsh':
        ov = int(a > 0x7fff)
        r = SATURATE(ov, 0, None, 0x00007fff, a)
    else:
        ov = int(a > 0xffff)
        r = SATURATE(ov, 0, None, 0x0000ffff, a)
    i.setD(r)
    i.st.ov(ov)


@simple('zvselh')
def _(i, n):
    cr0 = i.st.cr[0]
    ch, cl = (cr0 >> 3) & 1, (cr0 >> 2) & 1
    i.setD(join(H0(i.A) if ch else H0(i.B), H1(i.A) if cl else H1(i.B)))


def SL(v, cnt, w):
    return 0 if cnt > 31 else (v << cnt) & mask(w)


def MASKSS(n, w):
    return (mask(n + 1) << (w - n - 1)) & mask(w)


def MASKUS(n, w):
    return (mask(n) << (w - n)) & mask(w)


@simple('zvslh', 'zvslhi')
def _(i, n):
    if n == 'zvslhi':
        nh = nl = i.uimm
    else:
        nh, nl = fld(i.B, 43 - 32, 47 - 32, 32), fld(i.B, 59 - 32, 63 - 32, 32)
    i.setD(join(SL(H0(i.A), nh, 16), SL(H1(i.A), nl, 16)))


@simple('zvslhss', 'zvslhiss')
def _(i, n):
    out, ovs = [], 0
    for k, h in enumerate((H0(i.A), H1(i.A))):
        if n == 'zvslhiss':
            cnt, big = i.uimm, 0
        else:
            cnt = fld(i.B, 11 + 16 * k, 15 + 16 * k, 32)
            big = bit(i.B, 11 + 16 * k, 32)
        m = MASKSS(cnt, 16) if not big else 0xffff
        sgn = 0xffff if h >> 15 else 0
        ov = int((h & m) != (sgn & m))
        if big and h != 0:
            ov = 1
        out.append(SATURATE(ov, h >> 15, 0x8000, 0x7fff, SL(h, cnt, 16)))
        ovs |= ov
    i.setD(join(*out))
    i.st.ov(ovs)


@simple('zvslhus', 'zvslhius')
def _(i, n):
    out, ovs = [], 0
    for k, h in enumerate((H0(i.A), H1(i.A))):
        if n == 'zvslhius':
            cnt, big = i.uimm, 0
        else:
            cnt = fld(i.B, 11 + 16 * k, 15 + 16 * k, 32)
            big = bit(i.B, 11 + 16 * k, 32)
        m = MASKUS(cnt, 16) if not big else 0xffff
        ov = int((h & m) != 0)
        out.append(SATURATE(ov, 0, None, 0xffff, SL(h, cnt, 16)))
        ovs |= ov
    i.setD(join(*out))
    i.st.ov(ovs)


@simple('zslwss', 'zslwiss')
def _(i, n):
    a = i.A
    if n == 'zslwiss':
        cnt, big = i.uimm, 0
    else:
        cnt, big = fld(i.B, 58 - 32, 63 - 32, 32), bit(i.B, 58 - 32, 32)
    m = MASKSS(cnt, 32) if not big else M32
    sgn = M32 if a >> 31 else 0
    ov = int((a & m) != (sgn & m))
    if big and a != 0:
        ov = 1
    i.setD(SATURATE(ov, a >> 31, 0x80000000, 0x7fffffff, SL(a, cnt, 32)))
    i.st.ov(ov)


@simple('zslwus', 'zslwius')
def _(i, n):
    a = i.A
    if n == 'zslwius':
        cnt, big = i.uimm, 0
    else:
        cnt, big = fld(i.B, 58 - 32, 63 - 32, 32), bit(i.B, 58 - 32, 32)
    m = MASKUS(cnt, 32) if not big else M32
    ov = int((a & m) != 0)
    i.setD(SATURATE(ov, 0, None, 0xffffffff, SL(a, cnt, 32)))
    i.st.ov(ov)


@simple('zvsplatfih', 'zvsplatih')
def _(i, n):
    simm = i.rA
    v = (simm << 11) if n == 'zvsplatfih' else exts(simm, 5, 16)
    i.setD(join(v, v))


@simple('zvsrhis', 'zvsrhiu', 'zvsrhs', 'zvsrhu')
def _(i, n):
    if n in ('zvsrhis', 'zvsrhiu'):
        nh = nl = i.uimm
    else:
        nh, nl = fld(i.B, 43 - 32, 47 - 32, 32), fld(i.B, 59 - 32, 63 - 32, 32)
    signed = n in ('zvsrhis', 'zvsrhs')
    out = []
    for h, c in ((H0(i.A), nh), (H1(i.A), nl)):
        out.append((sval(h, 16) >> c) if signed else (h >> c))
    i.setD(join(*out))


@simple('zvunpkhgwsf', 'zvunpkhsf', 'zvunpkhsi', 'zvunpkhui', 'zunpkwgsf')
def _(i, n):
    a = i.A
    if n == 'zunpkwgsf':
        i.setpair(exts(a, 32, 48) << 16)
        return
    res = []
    for h in (H0(a), H1(a)):
        if n == 'zvunpkhgwsf':
            res.append(exts(h, 16, 24) << 8)
        elif n == 'zvunpkhsf':
            res.append(h << 16)
        elif n == 'zvunpkhsi':
            res.append(exts(h, 16, 32))
        else:
            res.append(h)
    i.setD(res[0])
    i.setD1(res[1])


@simple('zxtrw')
def _(i, n):
    nbits = (i.w & 3) * 8
    temp = (i.A << 32) | i.B
    i.setD(fld(temp, nbits, 31 + nbits, 64))


# ---------------------------------------------------------------------------
# Multiply and dot product, 1.6.5

TY = {'ui': 0, 'si': 1, 'sui': 2, 'smf': 3, 'u': 0, 's': 1, 'su': 2}


def hs_zmh(i, hs):
    src1 = H0(i.A) if hs in ('e', 'eo') else H1(i.A)
    src2 = H0(i.B) if hs == 'e' else H1(i.B)
    return src1, src2


def hs_zvmh(i, hs):
    A, B = i.A, i.B
    return {
        'ul': ((H0(A), H0(B)), (H1(A), H1(B))),
        'll': ((H1(A), H0(B)), (H1(A), H1(B))),
        'uu': ((H0(A), H0(B)), (H0(A), H1(B))),
        'xl': ((H1(A), H1(B)), (H0(A), H1(B))),
    }[hs]


def sel_dot(i, x):
    A, B = i.A, i.B
    if x:
        return (H1(A), H0(B)), (H0(A), H1(B))
    return (H0(A), H0(B)), (H1(A), H1(B))


def is_m1(a, b):
    return a == 0x8000 and b == 0x8000


def mult(i, n):
    st = i.st
    m = re.match(r'^zmh(e|eo|o)g(si|ui|sui|smf)(aa|an)?$', n)
    if m:   # 1.6.5.1-2
        hs, ty, acc = m.groups()
        s1, s2 = hs_zmh(i, hs)
        t = TY[ty]
        temp1 = mul(s1, s2, 16, t)
        temp2 = ext(temp1, 32, 64, t)
        if t == 3:
            # -1.0 * -1.0 is +1.0: 0x0000_0000_8000_0000
            temp2 = 0x80000000 if is_m1(s1, s2) else exts(temp1, 32, 64)
        if acc is None:
            i.setpair(temp2)
        else:
            i.setpair(i.pair() + temp2 if acc == 'aa' else i.pair() - temp2)
        return
    m = re.match(r'^zmh(e|eo|o)gwsmf(r?)(aa|an)?$', n)
    if m:   # 1.6.5.3-4
        hs, r, acc = m.groups()
        s1, s2 = hs_zmh(i, hs)
        if is_m1(s1, s2):
            temp2 = 0x00800000
        else:
            temp = exts(mul(s1, s2, 16, 3), 32, 33)
            if r:
                tempr = ROUND(temp, 8, 33)
                temp2 = exts(fld(tempr, 0, 24, 33), 25, 32)
            else:
                temp2 = exts(fld(temp, 0, 24, 33), 25, 32)
        if acc is None:
            i.setD(temp2)
        else:
            i.setD(i.D + temp2 if acc == 'aa' else i.D - temp2)
        return
    m = re.match(r'^zmh(e|eo|o)sf(r?)$', n)
    if m:   # 1.6.5.5
        hs, r = m.groups()
        s1, s2 = hs_zmh(i, hs)
        if is_m1(s1, s2):
            i.setD(0x7fff0000 if r else 0x7fffffff)
        else:
            temp = mul(s1, s2, 16, 3)
            if r:
                temp = ROUND(temp, 16, 32)
            i.setD(temp)
        return
    m = re.match(r'^zmh(e|eo|o)sf(r?)(aa|an)s$', n)
    if m:   # 1.6.5.6
        hs, r, acc = m.groups()
        s1, s2 = hs_zmh(i, hs)
        temp = 0x7fffffff if is_m1(s1, s2) else mul(s1, s2, 16, 3)
        if acc == 'aa':
            t = (exts(i.D, 32, 64) + exts(temp, 32, 64)) & mask(64)
        else:
            t = (exts(i.D, 32, 64) - exts(temp, 32, 64)) & mask(64)
        if r:
            t = ROUND(t, 16, 64)
        ov = chk_ovf(fld(t, 30, 32, 64), 3)
        i.setD(SATURATE(ov, bit(t, 30, 64), 0x80000000, 0x7fff0000 if r else 0x7fffffff,
                        fld(t, 32, 63, 64)))
        st.ov(ov)
        return
    m = re.match(r'^zmh(e|eo|o)(s|su|u)i$', n)
    if m:   # 1.6.5.7
        hs, ty = m.groups()
        s1, s2 = hs_zmh(i, hs)
        i.setD(mul(s1, s2, 16, TY[ty]))
        return
    m = re.match(r'^zmh(e|eo|o)(s|su|u)i(aa|an)$', n)
    if m:   # 1.6.5.8
        hs, ty, acc = m.groups()
        s1, s2 = hs_zmh(i, hs)
        temp = mul(s1, s2, 16, TY[ty])
        i.setD(i.D + temp if acc == 'aa' else i.D - temp)
        return
    m = re.match(r'^zmh(e|eo|o)(s|su|u)i(aa|an)s$', n)
    if m:   # 1.6.5.9
        hs, ty, acc = m.groups()
        s1, s2 = hs_zmh(i, hs)
        t = TY[ty]
        temp = mul(s1, s2, 16, t)
        if acc == 'aa':
            tt = (ext(i.D, 32, 64, t) + ext(temp, 32, 64, t)) & mask(64)
        else:
            tt = (ext(i.D, 32, 64, t) - ext(temp, 32, 64, t)) & mask(64)
        if t == 0:
            ov = bit(tt, 31, 64)
            i.setD(SATURATE(ov, bit(tt, 0, 64), 0, 0xffffffff, fld(tt, 32, 63, 64)))
        else:
            ov = bit(tt, 31, 64) ^ bit(tt, 32, 64)
            i.setD(SATURATE(ov, bit(tt, 0, 64), 0x80000000, 0x7fffffff, fld(tt, 32, 63, 64)))
        st.ov(ov)
        return
    if n in ('zvmhsfh', 'zvmhsfrh'):    # 1.6.5.10-11
        out = []
        for a, b in ((H0(i.A), H0(i.B)), (H1(i.A), H1(i.B))):
            if n == 'zvmhsfh':
                temp = 0x7fffffff if is_m1(a, b) else mul(a, b, 16, 3)
            else:
                temp = 0x7fff0000 if is_m1(a, b) else ROUND(mul(a, b, 16, 3), 16, 32)
            out.append(fld(temp, 0, 15, 32))
        i.setD(join(*out))
        return
    m = re.match(r'^zvmhsf(r?)(aa|an)hs$', n)
    if m:   # 1.6.5.12
        r, acc = m.groups()
        out, ovs = [], 0
        for a, b, d in ((H0(i.A), H0(i.B), H0(i.D)), (H1(i.A), H1(i.B), H1(i.D))):
            temp = 0x7fffffff if is_m1(a, b) else mul(a, b, 16, 3)
            if acc == 'aa':
                t = (exts(d << 16, 32, 34) + exts(temp, 32, 34)) & mask(34)
            else:
                t = (exts(d << 16, 32, 34) - exts(temp, 32, 34)) & mask(34)
            if r:
                t = ROUND(t, 16, 34)
            ov = chk_ovf(fld(t, 0, 2, 34), 3)
            out.append(SATURATE(ov, bit(t, 0, 34), 0x8000, 0x7fff, fld(t, 2, 17, 34)))
            ovs |= ov
        i.setD(join(*out))
        st.ov(ovs)
        return
    m = re.match(r'^zvmh(s|su|u)ih$', n)
    if m:   # 1.6.5.13
        out = []
        for a, b in ((H0(i.A), H0(i.B)), (H1(i.A), H1(i.B))):
            out.append(fld(mul(a, b, 16, 0), 16, 31, 32))
        i.setD(join(*out))
        return
    m = re.match(r'^zvmh(s|su|u)ihs$', n)
    if m:   # 1.6.5.14
        t = TY[m.group(1)]
        out, ovs = [], 0
        for a, b in ((H0(i.A), H0(i.B)), (H1(i.A), H1(i.B))):
            temp = mul(a, b, 16, t)
            if t == 0:
                ov = chk_ovfu(fld(temp, 0, 15, 32), 16)
                out.append(SATURATE(ov, 0, None, 0xffff, fld(temp, 16, 31, 32)))
            else:
                ov = chk_ovf(fld(temp, 0, 16, 32), 17)
                out.append(SATURATE(ov, bit(temp, 0, 32), 0x8000, 0x7fff, fld(temp, 16, 31, 32)))
            ovs |= ov
        i.setD(join(*out))
        st.ov(ovs)
        return
    m = re.match(r'^zvmh(s|su|u)i(aa|an)h$', n)
    if m:   # 1.6.5.15
        acc = m.group(2)
        out = []
        for a, b, d in ((H0(i.A), H0(i.B), H0(i.D)), (H1(i.A), H1(i.B), H1(i.D))):
            p = fld(mul(a, b, 16, 0), 16, 31, 32)
            out.append(d + p if acc == 'aa' else d - p)
        i.setD(join(*out))
        return
    m = re.match(r'^zvmh(s|su|u)i(aa|an)hs$', n)
    if m:   # 1.6.5.16
        t, acc = TY[m.group(1)], m.group(2)
        out, ovs = [], 0
        for a, b, d in ((H0(i.A), H0(i.B), H0(i.D)), (H1(i.A), H1(i.B), H1(i.D))):
            temp = mul(a, b, 16, t)
            if acc == 'aa':
                tt = (ext(d, 16, 34, t) + ext(temp, 32, 34, t)) & mask(34)
            else:
                tt = (ext(d, 16, 34, t) - ext(temp, 32, 34, t)) & mask(34)
            if t == 0:
                ov = chk_ovfu(fld(tt, 0, 17, 34), 18)
                out.append(SATURATE(ov, bit(tt, 0, 34), 0x0000, 0xffff, fld(tt, 18, 33, 34)))
            else:
                ov = chk_ovf(fld(tt, 0, 18, 34), 19)
                out.append(SATURATE(ov, bit(tt, 0, 34), 0x8000, 0x7fff, fld(tt, 18, 33, 34)))
            ovs |= ov
        i.setD(join(*out))
        st.ov(ovs)
        return
    m = re.match(r'^zmwg(s|su|u)i$', n)
    if m:   # 1.6.5.17
        i.setpair(mul(i.A, i.B, 32, TY[m.group(1)]))
        return
    m = re.match(r'^zmwg(s|su|u)i(aa|an)$', n)
    if m:   # 1.6.5.18
        temp = mul(i.A, i.B, 32, TY[m.group(1)])
        i.setpair(i.pair() + temp if m.group(2) == 'aa' else i.pair() - temp)
        return
    m = re.match(r'^zmwg(s|su|u)i(aa|an)s$', n)
    if m:   # 1.6.5.19
        t, acc = TY[m.group(1)], m.group(2)
        temp1 = mul(i.A, i.B, 32, t)
        if acc == 'aa':
            tt = (ext(i.pair(), 64, 66, t) + ext(temp1, 64, 66, t)) & mask(66)
        else:
            tt = (ext(i.pair(), 64, 66, t) - ext(temp1, 64, 66, t)) & mask(66)
        if t == 0:
            ov = bit(tt, 1, 66)
            i.setpair(SATURATE(ov, bit(tt, 0, 66), 0, 0xffffffffffffffff, fld(tt, 2, 65, 66)))
        else:
            ov = bit(tt, 1, 66) ^ bit(tt, 2, 66)
            i.setpair(SATURATE(ov, bit(tt, 0, 66), 0x8000000000000000, 0x7fffffffffffffff,
                               fld(tt, 2, 65, 66)))
        st.ov(ov)
        return
    m = re.match(r'^zmwgsmf(r?)(aa|an)?$', n)
    if m:   # 1.6.5.20-21
        r, acc = m.groups()
        if i.A == 0x80000000 and i.B == 0x80000000:
            temp2 = 0x0000800000000000
        else:
            temp1 = exts(mul(i.A, i.B, 32, 3), 64, 65)
            if r:
                tempr = ROUND(temp1, 16, 65)
                temp2 = exts(fld(tempr, 0, 48, 65), 49, 64)
            else:
                temp2 = exts(fld(temp1, 0, 48, 65), 49, 64)
        if acc is None:
            i.setpair(temp2)
        else:
            i.setpair(i.pair() + temp2 if acc == 'aa' else i.pair() - temp2)
        return
    m = re.match(r'^zmwl(s|su)is$', n)
    if m:   # 1.6.5.22
        temp1 = mul(i.A, i.B, 32, TY[m.group(1)])
        v = sval(temp1, 64)
        if v > 0x7fffffff or v < -0x80000000:
            mov = 1
            r = SATURATE(mov, bit(temp1, 0, 64), 0x80000000, 0x7fffffff, None)
        else:
            mov = 0
            r = fld(temp1, 32, 63, 64)
        i.setD(r)
        st.ov(mov)
        return
    if n == 'zmwluis':  # 1.6.5.23
        temp1 = mul(i.A, i.B, 32, 0)
        mov = int(temp1 > 0xffffffff)
        i.setD(SATURATE(mov, 0, None, 0xffffffff, temp1 & M32))
        st.ov(mov)
        return
    m = re.match(r'^zmwl(s|su|u)i(aa|an)$', n)
    if m:   # 1.6.5.24
        temp = mul(i.A, i.B, 32, TY[m.group(1)])
        i.setD(i.D + temp if m.group(2) == 'aa' else i.D - temp)
        return
    m = re.match(r'^zmwl(s|su|u)i(aa|an)s$', n)
    if m:   # 1.6.5.25
        t, acc = TY[m.group(1)], m.group(2)
        temp = mul(i.A, i.B, 32, t)
        if acc == 'aa':
            tt = (ext(i.D, 32, 65, t) + ext(temp, 64, 65, t)) & mask(65)
        else:
            tt = (ext(i.D, 32, 65, t) - ext(temp, 64, 65, t)) & mask(65)
        if t == 0:
            ov = chk_ovfu(fld(tt, 0, 32, 65), 33)
            i.setD(SATURATE(ov, bit(tt, 0, 65), 0, 0xffffffff, fld(tt, 33, 64, 65)))
        else:
            ov = chk_ovf(fld(tt, 0, 33, 65), 34)
            i.setD(SATURATE(ov, bit(tt, 0, 65), 0x80000000, 0x7fffffff, fld(tt, 33, 64, 65)))
        st.ov(ov)
        return
    m = re.match(r'^zmwsf(r?)$', n)
    if m:   # 1.6.5.26
        if i.A == 0x80000000 and i.B == 0x80000000:
            temp = 0x7fffffff00000000
        else:
            temp = mul(i.A, i.B, 32, 3)
        if m.group(1):
            temp = ROUND(temp, 32, 64)
        i.setD(fld(temp, 0, 31, 64))
        return
    m = re.match(r'^zmwsf(r?)(aa|an)s$', n)
    if m:   # 1.6.5.27
        r, acc = m.groups()
        if i.A == 0x80000000 and i.B == 0x80000000:
            temp1 = 0x7fffffffffffffff
        else:
            temp1 = mul(i.A, i.B, 32, 3)
        if acc == 'aa':
            temp2 = (exts(i.D << 32, 64, 66) + exts(temp1, 64, 66)) & mask(66)
        else:
            temp2 = (exts(i.D << 32, 64, 66) - exts(temp1, 64, 66)) & mask(66)
        if r:
            temp2 = ROUND(temp2, 32, 66)
        ov = chk_ovf(fld(temp2, 0, 2, 66), 3)
        i.setD(SATURATE(ov, bit(temp2, 0, 66), 0x80000000, 0x7fffffff, fld(temp2, 2, 33, 66)))
        st.ov(ov)
        return
    m = re.match(r'^zvmh(ul|ll|uu|xl)gwsmf(r?)(aa|an|anp)?$', n)
    if m:   # 1.6.5.28-29
        hs, r, acc = m.groups()
        res = []
        for s1, s2 in hs_zvmh(i, hs):
            if is_m1(s1, s2):
                res.append(0x00800000)
                continue
            temp = exts(mul(s1, s2, 16, 3), 32, 33)
            if r:
                temp = ROUND(temp, 8, 33)
            res.append(exts(fld(temp, 0, 24, 33), 25, 32))
        if acc is None:
            i.setD(res[0])
            i.setD1(res[1])
        else:
            oph, opl = {'aa': (1, 1), 'an': (-1, -1), 'anp': (-1, 1)}[acc]
            i.setD(i.D + oph * res[0])
            i.setD1(i.D1 + opl * res[1])
        return
    m = re.match(r'^zvmh(ul|ll|uu|xl)sf(r?)$', n)
    if m:   # 1.6.5.30
        hs, r = m.groups()
        res = []
        for s1, s2 in hs_zvmh(i, hs):
            if is_m1(s1, s2):
                res.append(0x7fff0000 if r else 0x7fffffff)
            else:
                temp = mul(s1, s2, 16, 3)
                res.append(ROUND(temp, 16, 32) if r else temp)
        i.setD(res[0])
        i.setD1(res[1])
        return
    m = re.match(r'^zvmh(ul|ll|uu|xl)sf(r?)(aa|an|anp)s$', n)
    if m:   # 1.6.5.31-32
        hs, r, acc = m.groups()
        ops = {'aa': ('+', '+'), 'an': ('-', '-'), 'anp': ('-', '+')}[acc]
        res, ovs = [], 0
        for (s1, s2), d, op in zip(hs_zvmh(i, hs), (i.D, i.D1), ops):
            temp = 0x7fffffff if is_m1(s1, s2) else mul(s1, s2, 16, 3)
            if not r:
                t = (exts(d, 32, 64) + exts(temp, 32, 64) if op == '+'
                     else exts(d, 32, 64) - exts(temp, 32, 64)) & mask(64)
                ov = bit(t, 31, 64) ^ bit(t, 32, 64)
                res.append(SATURATE(ov, bit(t, 31, 64), 0x80000000, 0x7fffffff, fld(t, 32, 63, 64)))
            else:
                t = (exts(d, 32, 34) + exts(temp, 32, 34) if op == '+'
                     else exts(d, 32, 34) - exts(temp, 32, 34)) & mask(34)
                tr = ROUND(t, 16, 34)
                ov = chk_ovf(fld(tr, 0, 2, 34), 3)
                res.append(SATURATE(ov, bit(tr, 0, 34), 0x80000000, 0x7fff0000, fld(tr, 2, 33, 34)))
            ovs |= ov
        i.setD(res[0])
        i.setD1(res[1])
        st.ov(ovs)
        return
    m = re.match(r'^zvmh(ul|ll|uu|xl)(s|su|u)i(aa|an|anp)?(s?)$', n)
    if m:   # 1.6.5.33-35
        hs, ty, acc, sat = m.groups()
        t = TY[ty]
        prods = [mul(s1, s2, 16, t) for s1, s2 in hs_zvmh(i, hs)]
        if acc is None:
            i.setD(prods[0])
            i.setD1(prods[1])
            return
        ops = {'aa': ('+', '+'), 'an': ('-', '-'), 'anp': ('-', '+')}[acc]
        if not sat:
            i.setD(i.D + prods[0] if ops[0] == '+' else i.D - prods[0])
            i.setD1(i.D1 + prods[1] if ops[1] == '+' else i.D1 - prods[1])
            return
        res, ovs = [], 0
        for p, d, op in zip(prods, (i.D, i.D1), ops):
            tt = (ext(d, 32, 64, t) + ext(p, 32, 64, t) if op == '+'
                  else ext(d, 32, 64, t) - ext(p, 32, 64, t)) & mask(64)
            if t == 0:
                ov = bit(tt, 31, 64)
                res.append(SATURATE(ov, bit(tt, 0, 64), 0, 0xffffffff, fld(tt, 32, 63, 64)))
            else:
                ov = bit(tt, 31, 64) ^ bit(tt, 32, 64)
                res.append(SATURATE(ov, bit(tt, 0, 64), 0x80000000, 0x7fffffff, fld(tt, 32, 63, 64)))
            ovs |= ov
        i.setD(res[0])
        i.setD1(res[1])
        st.ov(ovs)
        return
    m = re.match(r'^zvdotph(x?)g(a|s)(si|ui|sui|smf)(aa|an)?$', n)
    if m:   # 1.6.5.36-39
        x, sub, ty, acc = m.groups()
        t = TY[ty]
        ps = []
        for s1, s2 in sel_dot(i, x):
            if t == 3:
                # -1.0 * -1.0 is +1.0 before the extension
                ps.append(0x80000000 if is_m1(s1, s2) else exts(mul(s1, s2, 16, 3), 32, 64))
            else:
                ps.append(ext(mul(s1, s2, 16, t), 32, 64, t))
        temp = (ps[0] - ps[1] if sub == 's' else ps[0] + ps[1]) & mask(64)
        if acc is None:
            i.setpair(temp)
        else:
            i.setpair(i.pair() + temp if acc == 'aa' else i.pair() - temp)
        return
    m = re.match(r'^zvdotph(x?)(a|s)sf(r?)(aa|an)?s$', n)
    if m:   # 1.6.5.40-41, 46-47
        x, sub, r, acc = m.groups()
        ts = [0x7fffffff if is_m1(s1, s2) else mul(s1, s2, 16, 3) for s1, s2 in sel_dot(i, x)]
        dot = (exts(ts[0], 32, 64) - exts(ts[1], 32, 64) if sub == 's'
               else exts(ts[0], 32, 64) + exts(ts[1], 32, 64))
        if acc == 'aa':
            temp = (exts(i.D, 32, 64) + dot) & mask(64)
        elif acc == 'an':
            temp = (exts(i.D, 32, 64) - dot) & mask(64)
        else:
            temp = dot & mask(64)
        if r:
            temp = ROUND(temp, 16, 64)
        ov = chk_ovf(fld(temp, 30, 32, 64), 3)
        i.setD(SATURATE(ov, bit(temp, 30, 64), 0x80000000, 0x7fff0000 if r else 0x7fffffff,
                        fld(temp, 32, 63, 64)))
        st.ov(ov)
        return
    m = re.match(r'^zvdotph(x?)(a|s)(si|ui|sui)(aa|an)?(s?)$', n)
    if m:   # 1.6.5.42-45, 48-51
        x, sub, ty, acc, sat = m.groups()
        t = TY[ty]
        ph, pl = [mul(s1, s2, 16, t) for s1, s2 in sel_dot(i, x)]
        if not sat:
            temp = ph - pl if sub == 's' else ph + pl
            if acc is None:
                i.setD(temp)
            else:
                i.setD(i.D + temp if acc == 'aa' else i.D - temp)
            return
        e = (ext(ph, 32, 64, t) - ext(pl, 32, 64, t) if sub == 's'
             else ext(ph, 32, 64, t) + ext(pl, 32, 64, t))
        if acc is None:
            temp = e & mask(64)
            if t == 0:
                if sub == 's':
                    # 1.6.5.50: SATURATE(ov, temp0, 0x0000_0000, 0xFFFF_FFFF, temp32:63)
                    ov = bit(temp, 31, 64)
                    r = SATURATE(ov, bit(temp, 0, 64), 0, 0xffffffff, fld(temp, 32, 63, 64))
                else:
                    ov = bit(temp, 31, 64)
                    r = SATURATE(ov, 0, None, 0xffffffff, fld(temp, 32, 63, 64))
            else:
                ov = chk_ovf(fld(temp, 31, 32, 64), 2)
                r = SATURATE(ov, bit(temp, 31, 64), 0x80000000, 0x7fffffff, fld(temp, 32, 63, 64))
        else:
            d = ext(i.D, 32, 64, t)
            temp = (d + e if acc == 'aa' else d - e) & mask(64)
            if t == 0:
                ov = chk_ovfu(fld(temp, 30, 31, 64), 2)
                r = SATURATE(ov, bit(temp, 0, 64), 0, 0xffffffff, fld(temp, 32, 63, 64))
            else:
                ov = chk_ovf(fld(temp, 30, 32, 64), 3)
                r = SATURATE(ov, bit(temp, 0, 64), 0x80000000, 0x7fffffff, fld(temp, 32, 63, 64))
        i.setD(r)
        st.ov(ov)
        return
    m = re.match(r'^zvdotph(x?)gw(a|s)smf(r?)(aa|an)?$', n)
    if m:   # 1.6.5.52-55
        x, sub, r, acc = m.groups()
        ts = []
        for s1, s2 in sel_dot(i, x):
            ts.append(0x80000000 if is_m1(s1, s2) else exts(mul(s1, s2, 16, 3), 32, 34))
        temp1 = (ts[0] - ts[1] if sub == 's' else ts[0] + ts[1]) & mask(34)
        if r:
            tempr = ROUND(temp1, 8, 34)
            temp2 = exts(fld(tempr, 0, 25, 34), 26, 32)
        else:
            temp2 = exts(fld(temp1, 0, 25, 34), 26, 32)
        if acc is None:
            i.setD(temp2)
        else:
            i.setD(i.D + temp2 if acc == 'aa' else i.D - temp2)
        return
    raise KeyError(n)


# ---------------------------------------------------------------------------
# Loads and stores, 1.6.4

def calc_update(control, rb):
    offset = sval(fld(control, 35 - 32, 40 - 32, 32), 6)
    length = fld(control, 41 - 32, 50 - 32, 32)
    index = fld(control, 51 - 32, 63 - 32, 32)
    return (control & ~0x1fff & M32) | circinc(index, offset, length)


LOAD_SCALE = {
    'zldd': 8, 'zldw': 8, 'zldh': 8, 'zlwgsfd': 4, 'zlwwosd': 4, 'zlwhsplatwd': 4,
    'zlwhsplatd': 4, 'zlwhgwsfd': 4, 'zlwhed': 4, 'zlwhosd': 4, 'zlwhoud': 4, 'zlwh': 4,
    'zlww': 4, 'zlhgwsf': 2, 'zlhhsplat': 2, 'zlhhe': 2, 'zlhhos': 2, 'zlhhou': 2,
    'zstdd': 8, 'zstdw': 8, 'zstdh': 8, 'zstwhed': 4, 'zstwhod': 4, 'zstwh': 4, 'zstww': 4,
    'zsthe': 2, 'zstho': 2,
}
LDST_RE = re.compile(r'^(' + '|'.join(sorted(LOAD_SCALE, key=len, reverse=True)) + r')(u|x|mx)?$')


def ldst(i, n):
    m = LDST_RE.match(n)
    base, form = m.group(1), m.group(2) or ''
    st = i.st
    A = i.A
    if form in ('', 'u'):
        b = 0 if (i.rA == 0 and form == '') else A
        ea = (b + i.uimm * LOAD_SCALE[base]) & M32
    elif form == 'x':
        ea = ((0 if i.rA == 0 else A) + i.B) & M32
    else:
        ea = ((A & 0x1fff) + i.B) & M32
    rdm = st.rd
    if base == 'zldd':
        i.setpair(rdm(ea, 8))
    elif base == 'zldw':
        i.setD(rdm(ea, 4))
        i.setD1(rdm(ea + 4, 4))
    elif base == 'zldh':
        i.setD(join(rdm(ea, 2), rdm(ea + 2, 2)))
        i.setD1(join(rdm(ea + 4, 2), rdm(ea + 6, 2)))
    elif base == 'zlwgsfd':
        temp = rdm(ea, 4)
        i.setD((0xffff0000 if temp >> 31 else 0) | fld(temp, 0, 15, 32))
        i.setD1(fld(temp, 16, 31, 32) << 16)
    elif base == 'zlwwosd':
        i.setD1(rdm(ea, 4))
        i.setD(M32 if i.D1 >> 31 else 0)
    elif base == 'zlwhsplatwd':
        i.setD(join(rdm(ea, 2), rdm(ea + 2, 2)))
        i.setD1(join(rdm(ea, 2), rdm(ea + 2, 2)))
    elif base == 'zlwhsplatd':
        i.setD(join(rdm(ea, 2), rdm(ea, 2)))
        i.setD1(join(rdm(ea + 2, 2), rdm(ea + 2, 2)))
    elif base == 'zlwhgwsfd':
        for setter, off in ((i.setD, 0), (i.setD1, 2)):
            h = rdm(ea + off, 2)
            setter(((0xff if h >> 15 else 0) << 24) | (h << 8))
    elif base == 'zlwhed':
        i.setD(join(rdm(ea, 2), 0))
        i.setD1(join(rdm(ea + 2, 2), 0))
    elif base == 'zlwhosd':
        i.setD(exts(rdm(ea, 2), 16, 32))
        i.setD1(exts(rdm(ea + 2, 2), 16, 32))
    elif base == 'zlwhoud':
        i.setD(join(0, rdm(ea, 2)))
        i.setD1(join(0, rdm(ea + 2, 2)))
    elif base == 'zlwh':
        i.setD(join(rdm(ea, 2), rdm(ea + 2, 2)))
    elif base == 'zlww':
        i.setD(rdm(ea, 4))
    elif base == 'zlhgwsf':
        h = rdm(ea, 2)
        i.setD(((0xff if h >> 15 else 0) << 24) | (h << 8))
    elif base == 'zlhhsplat':
        h = rdm(ea, 2)
        i.setD(join(h, h))
    elif base == 'zlhhe':
        i.setD(join(rdm(ea, 2), 0))
    elif base == 'zlhhos':
        i.setD(exts(rdm(ea, 2), 16, 32))
    elif base == 'zlhhou':
        i.setD(join(0, rdm(ea, 2)))
    elif base == 'zstdd':
        st.wr(ea, 8, (i.D << 32) | i.D1)
    elif base == 'zstdw':
        st.wr(ea, 4, i.D)
        st.wr(ea + 4, 4, i.D1)
    elif base == 'zstdh':
        st.wr(ea, 2, H0(i.D))
        st.wr(ea + 2, 2, H1(i.D))
        st.wr(ea + 4, 2, H0(i.D1))
        st.wr(ea + 6, 2, H1(i.D1))
    elif base == 'zstwhed':
        st.wr(ea, 2, H0(i.D))
        st.wr(ea + 2, 2, H0(i.D1))
    elif base == 'zstwhod':
        st.wr(ea, 2, H1(i.D))
        st.wr(ea + 2, 2, H1(i.D1))
    elif base == 'zstwh':
        st.wr(ea, 2, H0(i.D))
        st.wr(ea + 2, 2, H1(i.D))
    elif base == 'zstww':
        st.wr(ea, 4, i.D)
    elif base == 'zsthe':
        st.wr(ea, 2, H0(i.D))
    elif base == 'zstho':
        st.wr(ea, 2, H1(i.D))
    else:
        raise KeyError(n)
    if form == 'u':
        i.setA(ea)
    elif form == 'mx':
        i.setA(calc_update(A, i.B))


def execute(name, word, st):
    i = Insn(st, word)
    if name in SIMPLE:
        SIMPLE[name](i, name)
    elif LDST_RE.match(name):
        ldst(i, name)
    else:
        mult(i, name)
