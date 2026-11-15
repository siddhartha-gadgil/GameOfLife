#!/usr/bin/env python3
"""Cross-check of LeanTheory/Theory/Life/LayoutPieces.lean (untrusted oracle; numerical check only).

The Lean module defines `LP.machPieces p`: every periodic piece of the Life machine of a counter
program at time 0, each as `Piece.place base vx vy phase`, with positions given by the closed
formulas of LayoutLP.lean (layout `LP` of report R-31) and phases by the world-line arithmetic of
`p1_layout.py` (re-implemented in Lean).  This script re-implements the Lean definitions in
Python, line by line (same integer arithmetic: positive divisors only, so Lean's `/` and `%` are
Python's `//` and `%`), and compares, for the test programs of R-31 (`add`, `share`, `rand`):

  (1) the OR gate and the 8 reflector images (cells parsed from the Lean sources) against the
      pieces ('asm', 0, 0, 0, 0) and ('rf', k, 0, 0, 0) of scripts/life_lp at time 0;
  (2) the placement: the placed pieces (base, vx, vy, phase), with the cells of every base parsed
      from the Lean sources (bodies, register circuit, stations, eaters included) and evolved
      `phase` generations, give at time 0 exactly the cells of `p1_layout.layout(program)` (all
      pieces at time 0 plus the eater cells), and the numbers of pieces agree (grouped bases
      counted by their members);
  (3) with `--lean DIR` (needs the built module LeanTheory.Theory.Life.LayoutPieces): the list
      `LP.machSpecs p` evaluated by Lean (a file written to DIR, run by `lake env lean`) equals
      this re-implementation, spec by spec (base, translation, phase).

With `--sweep K` the random programs 0 … K-1 of `p5_formulas.py` (seed 11) are checked as well.

Usage: layout_pieces_check.py [--lean DIR] [--sweep K] [add share rand ...]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..')
sys.path.insert(0, os.path.join(HERE, '..', 'life_lp'))
import p1_layout  # noqa: E402
from lpcommon import piece_cells, step_cells, translate  # noqa: E402

LEAN = os.path.join(ROOT, 'LeanTheory', 'Theory', 'Life')

# ------------------------------------------------------------------------------------------------
# Lean base pieces: parse `def NAME : Finset Cell := ofRows X Y [rows]` from the sources
# ------------------------------------------------------------------------------------------------


def cells_of_window(x0, y0, rows):
    out = set()
    for i, r in enumerate(rows):
        j = 0
        while r:
            if r & 1:
                out.add((x0 + j, y0 + i))
            r >>= 1
            j += 1
    return out


def parse_defs(path):
    src = open(path).read()
    out = {}
    pat = re.compile(r'def (\w+) : Finset Cell :=\s*ofRows \(?(-?\d+)\)? \(?(-?\d+)\)?\s*\[([^\]]*)\]')
    for m in pat.finditer(src):
        rows = [int(x) for x in m.group(4).replace('\n', ' ').split(',') if x.strip()]
        out[m.group(1)] = cells_of_window(int(m.group(2)), int(m.group(3)), rows)
    return out


def parse_stage_G(path):
    src = open(path).read()
    out = {}
    pat = re.compile(r'def (rf0\w+) : Stage where\s*G := ofRows \(?(-?\d+)\)? \(?(-?\d+)\)? \[([^\]]*)\]')
    for m in pat.finditer(src):
        rows = [int(x) for x in m.group(4).split(',')]
        out[m.group(1)] = cells_of_window(int(m.group(2)), int(m.group(3)), rows)
    return out


RF_NAMES = ['rf0SWNW', 'rf0NWNE', 'rf0NESE', 'rf0SESW', 'rf0SENE', 'rf0NWSW', 'rf0NENW', 'rf0SWSE']


def lean_bases():
    B = {}
    B['orGate'] = parse_defs(os.path.join(LEAN, 'MergeChain.lean'))['orGate']
    st = parse_stage_G(os.path.join(LEAN, 'Rf0Images.lean'))
    for k, nm in enumerate(RF_NAMES):
        B['rf%d' % k] = st[nm]
    for nm, c in parse_defs(os.path.join(LEAN, 'StationChain.lean')).items():
        if re.fullmatch(r'st(NZ|Z)P\d', nm):
            B[nm] = c
    for f, pre, n in (('BodyDecData.lean', 'bodyDec', 8), ('BodyIncData.lean', 'bodyInc', 3),
                      ('Dz2gData.lean', 'dz2g', 28)):
        d = parse_defs(os.path.join(LEAN, 'Gen', f))
        for i in range(n):
            B['%sG%d' % (pre, i)] = d['%sR%d' % (pre, i)]
    lp = parse_defs(os.path.join(LEAN, 'LayoutPieces.lean'))
    B['eatNZEnd'] = lp['eatNZEndR']
    B['eatZEnd'] = lp['eatZEndR']
    return B


_CYC = {}


def base_phase(B, name, ph):
    key = (name, ph)
    if key not in _CYC:
        c = B[name] if ph == 0 else step_cells(base_phase(B, name, ph - 1))
        _CYC[key] = frozenset(c)
    return _CYC[key]

# ------------------------------------------------------------------------------------------------
# Re-implementation of the Lean definitions (LayoutLP.lean + LayoutPieces.lean)
# ------------------------------------------------------------------------------------------------


def fixp(c, pi):
    return c - (c - pi) % 2


def ceil30(x):
    return (x + 29) // 30


def ceil120(x):
    return (x + 119) // 120


class Prog:
    """`LP` parameters of a program (LayoutLP.lean)."""

    def __init__(self, prog):
        self.prog = prog
        self.Nn = len(prog)
        rb = [ins[1] + 1 for ins in prog if ins[0] != 'halt']
        self.R = max(1, max(rb + [0]))
        self.D = max(1, max([self.decCount(r) for r in range(self.R)] + [0]))
        self.P = max(1, max([self.predCount(a) for a in range(self.Nn + self.R)] + [0]))

    def decCount(self, r):
        return sum(1 for ins in self.prog if ins[0] == 'dec' and ins[1] == r)

    def predContrib(self, a, i):
        ins = self.prog[i]
        if ins[0] == 'inc':
            return (1 if i + 1 == a else 0) + (1 if self.Nn + ins[1] == a else 0)
        if ins[0] == 'dec':
            return (1 if i + 1 == a else 0) + (1 if ins[2] == a else 0)
        return 0

    def predBefore(self, a, i):
        return sum(self.predContrib(a, k) for k in range(i))

    def predCount(self, a):
        return (1 if a == 0 else 0) + self.predBefore(a, self.Nn)

    def callerIdx(self, r, i):
        return sum(1 for k in range(i) if self.prog[k][0] == 'dec' and self.prog[k][1] == r)

    # --- LayoutLP formulas
    def PU(self):
        return 540 + 180 * self.P

    def A(self, a):
        return self.PU() * a

    def NB(self):
        return 2 + self.Nn + self.R

    def VT(self):
        return -30 * ceil30(3444 + 198 * self.D + 660 * self.NB())

    def VU(self):
        return self.VT() - 1644

    def PM(self):
        return 2400 + 540 * self.D

    def slabR(self):
        return max(238, 86 + 58 * self.P)

    def U0(self):
        return 30 * ceil30(self.PU() * (self.Nn + self.R - 1) + self.slabR() + 943 + 248 * self.D)

    def U(self, r):
        return self.U0() + self.PM() * r

    def HI(self):
        return 30 * ((-716 - 122 * self.P) // 30)

    def decPortV(self, t):
        return -3351 - 99 * (2 * self.D - 1 - t)

    def leftChan(self, idx, v):
        return fixp(-793 - 62 * idx, 1 - v % 2)

    def decChan(self, t):
        return self.leftChan(t, self.decPortV(t))

    def incChan(self):
        return self.leftChan(2 * self.D, -2347)

    def nzTokChan(self, j):
        return self.leftChan(2 * self.D + 1 + 2 * j, 1256 + 144 * j)

    def nzAnsChan(self, j):
        return self.leftChan(2 * self.D + 2 + 2 * j, 1325 + 144 * j)

    def qOf(self, j):
        return self.D - 1 - j

    def uR(self):
        return 1410 + 144 * self.D

    def zAnsDepth(self, j):
        return fixp(1500 + 180 * self.qOf(j), 1 - (1301 + 144 * j) % 2)

    def zTokDepth(self, j):
        return self.zAnsDepth(j) + 61

    def zAnsChan(self, j):
        return fixp(self.uR() + 124 * self.qOf(j), 1 - self.zAnsDepth(j) % 2)

    def zTokChan(self, j):
        return fixp(self.uR() + 124 * self.qOf(j) + 62, 1 - self.zTokDepth(j) % 2)

    def track(self, b, k, pi):
        return self.VT() + 660 * b + 62 * k + pi

    def trackOut(self, b, s, c):
        return self.track(b, s, 1 - c % 2)

    def trackBack(self, b, s, c):
        return self.track(b, 9 - s, 1 - c % 2)

    def hairReg(self, s, e, c):
        return fixp(self.HI() + 90 * s - 2 * e, c % 2)

    def hairCont(self, G, e, c):
        return fixp(self.HI() - 62 - G - 2 * e, c % 2)

    def hairC(self, q, c):
        return fixp(self.HI() + 90 - 2 * eCtot(q), c % 2)

    def hairKNZ(self, q, cC, c):
        return fixp(self.hairC(q, cC) - 62 - 2 * eN(q), c % 2)


def eC(q):
    return 9 * q % 15


def sigma(q):
    return 2 * (q % 2)


def xC(q):
    return max(0, ceil120(368 + 1564 * q - 8 * eC(q) - 30 * sigma(q)))


def eCtot(q):
    return eC(q) + 4 * sigma(q) + 15 * xC(q)


def eN(q):
    return (3936 + 228 * q - 2 * sigma(q)) // 8


def dZ0(q):
    return 367 + 1564 * q - 8 * eC(q)


def eKZ(q):
    return (-1 - dZ0(q) + 30 * sigma(q) + 120 * xC(q)) // 8


def winE(r0, rho):
    return 2 * (rho - r0) % 15


def rhoStar(r0):
    return 4 + r0 % 2


# --- world lines (dx, dy, lane, tau) and the reflector images ------------------------------------
SE, SW, NW, NE = (1, 1), (-1, 1), (-1, -1), (1, -1)


def shiftWL(w, p, q, s):
    (dx, dy), lane, tau = w
    return ((dx, dy), lane + dy * p - dx * q, tau + s - 4 * dx * p)


# image k: (input world line, output world line, corner (u0, v0) of the copy at the origin)
RF_IN = [(SW, 19, 18), (NW, 22, -68), (NE, 23, 26), (SE, 22, -60), (SE, -21, 26), (NW, -21, 18),
         (NE, -20, -60), (SW, -24, -68)]
RF_OUT = [(NW, -14, 13), (NE, -13, -37), (SE, -14, 21), (SW, -17, -45), (NE, 16, 21), (SW, 12, 13),
          (NW, 15, -45), (SE, 15, -37)]
RF_CU = [14, -22, -14, 22, -21, 21, -15, 15]
RF_CV = [19, 13, -23, -17, -16, 12, 20, -24]


def rfX(k, cu, cv):
    return (cu - RF_CU[k] + cv - RF_CV[k]) // 2


def rfY(k, cu, cv):
    return (cv - RF_CV[k] - (cu - RF_CU[k])) // 2


def reflect(g, k, cu, cv):
    """(placed piece, outgoing glider): image k with its corner at (cu, cv), in phase with g."""
    p, q = rfX(k, cu, cv), rfY(k, cu, cv)
    s = g[2] - RF_IN[k][2] + 4 * RF_IN[k][0][0] * p
    return ('rf%d' % k, p, q, (-s) % 30), shiftWL(RF_OUT[k], p, q, s)


def route(g, corners):
    """corners: [(k, cu, cv)]; returns (pieces, final glider, gliders after each corner)."""
    pcs, legs = [], [g]
    for (k, cu, cv) in corners:
        pc, g = reflect(g, k, cu, cv)
        pcs.append(pc)
        legs.append(g)
    return pcs, g, legs


def timeUV(w, u, v):
    (dx, dy), lane, tau = w
    return tau + (dx - dy) * u + (dx + dy) * v + 2 * dx * dy * lane


# --- unit templates ------------------------------------------------------------------------------
C0 = {'dec': -237, 'inc': -91, 'halt': -67, 'merge': -67}
IO0 = {('dec', 'L'): (SE, -155, 2665), ('dec', 'R'): (SE, 127, 1221), ('dec', 'D'): (SE, 188, 787),
       ('inc', 'R'): (SE, 157, 1029), ('inc', 'D'): (SE, 68, 605), ('halt', 'D'): (SE, 14, 629),
       ('merge', 'D'): (SE, 14, 629)}


def unitDX(m, a):
    return (m.A(a) + m.VU()) // 2


def unitDY(m, a):
    return (m.VU() - m.A(a)) // 2


def sideWL(t):
    return (NE, -76 + 99 * t, 1 + 140 * t + (16 * t) % 30)


def mergeOut(t):
    return (SE, 14, 629 + 254 * t + (16 * t) % 30)


def kindOf(m, a):
    if a < m.Nn:
        ins = m.prog[a]
        return ins[0]
    return 'merge'


def mergeUsed(m, r):
    return any(ins[0] == 'inc' and ins[1] == r for ins in m.prog)


def unitPieces(m, a):
    kind = kindOf(m, a)
    dx, dy = unitDX(m, a), unitDY(m, a)
    out = []
    for t in range(2 * m.P):
        out.append(('orGate', dx - 35 * t, dy - 64 * t, (14 * t) % 30))
    if kind == 'dec':
        out += [('bodyDecG%d' % i, dx, dy, 0) for i in range(8)]
    if kind == 'inc':
        out += [('bodyIncG%d' % i, dx, dy, 0) for i in range(3)]
    return out


# --- module --------------------------------------------------------------------------------------
def modulePieces(m, r):
    dx, dy = m.U(r) // 2, -(m.U(r) // 2)
    D = m.D
    out = [('dz2gG%d' % i, dx, dy, 0) for i in range(28)]
    out.append(('rf4', dx - 850, dy - 1044, 25))
    out.append(('orGate', dx - 1132, dy - 1291, 16))
    for mm in range(2 * D):
        out.append(('orGate', dx - 1700 - 35 * mm, dy - 1727 - 64 * mm, (15 + 14 * mm) % 30))
    for j in range(D):
        for i in range(3):
            out.append(('stNZP%d' % i, dx + 72 * j, dy + 72 * j, (12 * j) % 30))
    for j in range(D):
        for i in range(3):
            out.append(('stZP%d' % i, dx + 72 * j, dy - 72 * j, (12 * j) % 30))
    out.append(('eatNZEnd', dx + 72 * (D - 1), dy + 72 * (D - 1), 0))
    out.append(('eatZEnd', dx + 72 * (D - 1), dy - 72 * (D - 1), 0))
    return out


def modWL(m, r, w):
    return shiftWL(w, m.U(r) // 2, -(m.U(r) // 2), 0)


def decWin(m, r, t):
    mm = 2 * m.D - 1 - t
    return modWL(m, r, (NE, 3351 + 99 * mm, 6801 + 140 * mm + (15 + 16 * mm) % 30))


def cprimeWL(m, r, t):
    mm = 2 * m.D - 1 - t
    return modWL(m, r, (SE, 41, 7429 + 254 * mm + (15 + 16 * mm) % 30))


INC_WIN = (NE, 2347, 4543)
CP0 = (SE, 41, 4444)


def nzAnsWL(j):
    return (SW, 1325 + 144 * j, 12547 + 576 * j)


def zAnsWL(j):
    return (SE, 1301 + 144 * j, 9025)


# --- links ---------------------------------------------------------------------------------------
def upCorners(m, b, s, cs, H, cd, vt):
    o, bk = m.trackOut(b, s, cs), m.trackBack(b, s, cs)
    return [(3, cs, o), (7, H, o), (4, H, bk), (6, cd, bk), (1, cd, vt)]


def downCorners(m, b, s, cs, H, cd, vp):
    o, bk = m.trackOut(b, s, cs), m.trackBack(b, s, cs)
    return [(3, cs, o), (7, H, o), (4, H, bk), (2, cd, bk), (4, cd, vp)]


def ztokCorners(m, b, s, cs, H, cd, wd, st):
    o, bk = m.trackOut(b, s, cs), m.trackBack(b, s, cs)
    return [(3, cs, o), (7, H, o), (4, H, bk), (2, cd, bk), (3, cd, wd), (0, st, wd)]


def ansTail(m, b, s, c, H, cd, vt):
    o, bk = m.trackOut(b, s, c), m.trackBack(b, s, c)
    return [(5, c, o), (7, H, o), (4, H, bk), (6, cd, bk), (1, cd, vt)]


def nzAnsCorners(m, b, r, j, H, cd, vt):
    c = m.U(r) + m.nzAnsChan(j)
    return [(0, c, 1325 + 144 * j)] + ansTail(m, b, 3, c, H, cd, vt)


def zAnsCorners(m, b, r, j, H, cd, vt):
    c = m.U(r) + m.zAnsChan(j)
    return [(4, m.U(r) + 1301 + 144 * j, m.zAnsDepth(j)), (6, c, m.zAnsDepth(j))] + \
        ansTail(m, b, 4, c, H, cd, vt)


def predIdx(m, a, i, off):
    return (1 if a == 0 else 0) + m.predBefore(a, i) + off


def copyIdx(C0_, e, c):
    return 2 * e + (C0_ - c) % 2


class Dest:
    """Entry copy t of unit a for a link from column c."""

    def __init__(self, m, a, e, c):
        self.a = a
        self.t = copyIdx(C0[kindOf(m, a)], e, c)
        self.cd = m.A(a) + C0[kindOf(m, a)] - 61 * self.t
        self.vt = m.VU() + 76 - 99 * self.t
        self.win = shiftWL(sideWL(self.t), unitDX(m, a), unitDY(m, a), 0)


def unitWL(m, a, o):
    return shiftWL(IO0[(kindOf(m, a), o)], unitDX(m, a), unitDY(m, a), 0)


def winRes(g, w):
    return (g[2] - w[2]) % 30


def slot(g, w):
    return (g[2] - w[2]) // 30


def solveE(m, g0, mk, win):
    """The window rule: route with e = 0, residue r0, e = winE r0 (rhoStar r0)."""
    _, g, _ = route(g0, mk(0))
    r0 = winRes(g, win)
    return winE(r0, rhoStar(r0))


def linkPieces(m):
    """All route reflectors, by instruction (then merge links): list of (name, pieces)."""
    out = []
    for i, ins in enumerate(m.prog):
        b = 1 + i
        if ins[0] == 'halt':
            cs = m.A(i) + 14
            pcs, _, _ = route(unitWL(m, i, 'D'), [(3, cs, m.trackOut(0, 0, cs))])
            out.append(('halt%d' % i, pcs))
        elif ins[0] == 'inc':
            r = ins[1]
            a = m.Nn + r
            # INC link (slot 1) to the merge unit N + r
            csl = m.A(i) + 157
            dl = Dest(m, a, predIdx(m, a, i, 1 if i + 1 == a else 0), csl)

            def mkl(e):
                return upCorners(m, b, 1, csl, m.hairReg(1, e, csl), dl.cd, dl.vt)
            el = solveE(m, unitWL(m, i, 'R'), mkl, dl.win)
            pl, gl, _ = route(unitWL(m, i, 'R'), mkl(el))
            # the merge link of r from this activation: INC control time at the INC gate
            gm = shiftWL(shiftWL(mergeOut(dl.t), unitDX(m, a), unitDY(m, a), 0), 0, 0,
                         30 * (slot(gl, dl.win) - 20))
            em = mergeE(m, r)
            _, g2, _ = route(gm, mergeCorners(m, r, em))
            tinc = timeUV(g2, m.U(r) - 1087 + 1260, m.U(r) - 1087 - 1260)
            # INC continue (slot 0) to unit i + 1, far hairpin G
            csc = m.A(i) + 68
            dc = Dest(m, i + 1, predIdx(m, i + 1, i, 0), csc)

            def mkc(e, G):
                return upCorners(m, b, 0, csc, m.hairCont(G, e, csc), dc.cd, dc.vt)
            ec0 = solveE(m, unitWL(m, i, 'D'), lambda e: mkc(e, 0), dc.win)
            _, _, legs = route(unitWL(m, i, 'D'), mkc(ec0, 0))
            t0 = timeUV(legs[3], dc.cd, m.trackBack(b, 0, csc))
            G = 30 * ceil120(max(0, tinc + 500 - t0))
            ec = solveE(m, unitWL(m, i, 'D'), lambda e: mkc(e, G), dc.win)
            pc, _, _ = route(unitWL(m, i, 'D'), mkc(ec, G))
            out.append(('inc%d.cont' % i, pc))
            out.append(('inc%d.link' % i, pl))
        else:
            r, z = ins[1], ins[2]
            j = m.callerIdx(r, i)
            q = m.qOf(j)
            U = m.U(r)
            cN, cC, cZ = m.A(i) - 155, m.A(i) + 127, m.A(i) + 188
            HC = m.hairC(q, cC)
            pN, _, _ = route(unitWL(m, i, 'L'),
                             downCorners(m, b, 0, cN, m.hairKNZ(q, cC, cN), U + m.nzTokChan(j),
                                         1256 + 144 * j))
            pC, gC, _ = route(unitWL(m, i, 'R'),
                              downCorners(m, b, 1, cC, HC, U + m.decChan(2 * j), m.decPortV(2 * j)))
            pZ, _, _ = route(unitWL(m, i, 'D'),
                             ztokCorners(m, b, 2, cZ, m.hairReg(2, eKZ(q), cZ), U + m.zTokChan(j),
                                         m.zTokDepth(j), U + 1230 + 144 * j))
            cp = shiftWL(cprimeWL(m, r, 2 * j), 0, 0, 30 * (slot(gC, decWin(m, r, 2 * j)) - 20))
            shift = cp[2] - modWL(m, r, CP0)[2]
            # NZ answer (slot 3) to unit i + 1, Z answer (slot 4) to unit z
            gN = shiftWL(modWL(m, r, nzAnsWL(j)), 0, 0, shift)
            cAN = U + m.nzAnsChan(j)
            dN = Dest(m, i + 1, predIdx(m, i + 1, i, 0), cAN)

            def mkN(e):
                return nzAnsCorners(m, b, r, j, m.hairReg(3, e, cAN), dN.cd, dN.vt)
            eA = solveE(m, gN, mkN, dN.win)
            pNA, _, _ = route(gN, mkN(eA))
            gZ = shiftWL(modWL(m, r, zAnsWL(j)), 0, 0, shift)
            cAZ = U + m.zAnsChan(j)
            dZ = Dest(m, z, predIdx(m, z, i, 1 if i + 1 == z else 0), cAZ)

            def mkZ(e):
                return zAnsCorners(m, b, r, j, m.hairReg(4, e, cAZ), dZ.cd, dZ.vt)
            eB = solveE(m, gZ, mkZ, dZ.win)
            pZA, _, _ = route(gZ, mkZ(eB))
            out += [('dec%d.KNZ' % i, pN), ('dec%d.C' % i, pC), ('dec%d.KZ' % i, pZ),
                    ('dec%d.nz' % i, pNA), ('dec%d.z' % i, pZA)]
    for r in range(m.R):
        if mergeUsed(m, r):
            pcs, _, _ = route(unitWL(m, m.Nn + r, 'D'), mergeCorners(m, r, mergeE(m, r)))
            out.append(('merge%d' % r, pcs))
    return out


def mergeCorners(m, r, e):
    a = m.Nn + r
    cs = m.A(a) + 14
    return downCorners(m, 1 + m.Nn + r, 0, cs, m.hairReg(0, e, cs), m.U(r) + m.incChan(), -2347)


def mergeE(m, r):
    return solveE(m, unitWL(m, m.Nn + r, 'D'), lambda e: mergeCorners(m, r, e),
                  modWL(m, r, INC_WIN))


def machPieces(prog):
    m = Prog(prog)
    out = []
    for a in range(m.Nn + m.R):
        if a < m.Nn or mergeUsed(m, a - m.Nn):
            out += unitPieces(m, a)
    for r in range(m.R):
        out += modulePieces(m, r)
    for _, pcs in linkPieces(m):
        out += pcs
    return m, out

# ------------------------------------------------------------------------------------------------
# Comparison
# ------------------------------------------------------------------------------------------------


def check_bases(B):
    """Lean bases against the pieces of scripts/life_lp at time 0."""
    ok = True
    ref = {'orGate': [('asm', 0, 0, 0, 0)]}
    for k in range(8):
        ref['rf%d' % k] = [('rf', k, 0, 0, 0)]
    for nm, c in sorted(ref.items()):
        pc = set().union(*[piece_cells(p, 0) for p in c])
        good = pc == B[nm]
        ok &= good
        print('  base %-8s = %s at time 0: %s' % (nm, c[0], good))
    return ok


def compare(name, prog):
    ref = p1_layout.layout(prog)
    B = lean_bases()
    m, lean = machPieces(prog)
    cells = set()
    for (b, vx, vy, ph) in lean:
        cells |= set(translate(base_phase(B, b, ph), vx, vy))
    want = set(ref.eaters)
    for p in ref.pieces:
        want |= set(piece_cells(p, 0))
    nref = len(ref.pieces)
    # grouped Lean bases count their members: dz2g groups 42 pieces, bodies, stations 2 + eater
    grp = {'dz2gG0': 12, 'dz2gG1': 2, 'dz2gG3': 3}
    nlean = 0
    for (b, _, _, _) in lean:
        if b.startswith('dz2gG'):
            nlean += grp.get(b, 1)
        elif b in ('stNZP2', 'stZP2', 'eatNZEnd', 'eatZEnd'):
            nlean += 0
        else:
            nlean += 1
    same = cells == want
    print('%s: N %d R %d D %d P %d; Lean %d placed pieces (%d machine pieces), p1_layout %d pieces '
          '+ %d eater cells; cells at time 0 equal: %s (Lean %d cells, p1_layout %d, '
          'only Lean %d, only p1_layout %d)' % (
              name, m.Nn, m.R, m.D, m.P, len(lean), nlean, nref, len(ref.eaters), same,
              len(cells), len(want), len(cells - want), len(want - cells)))
    return same and nlean == nref


LEAN_PROG = {'inc': lambda ins: '.inc %d' % ins[1], 'dec': lambda ins: '.decJz %d %d' % ins[1:],
             'halt': lambda ins: '.halt'}
BASE_NAME = {'orGate': 'orGate', 'rf': 'rf%s', 'bodyDec': 'bodyDecG%s', 'bodyInc': 'bodyIncG%s',
             'dz2g': 'dz2gG%s', 'stNZ': 'stNZP%s', 'stZ': 'stZP%s', 'eatNZ': 'eatNZEnd',
             'eatZ': 'eatZEnd'}


def lean_eval(progs, tmpdir):
    """Evaluate `LP.machSpecs` in Lean (needs the built module) on the programs `progs`."""
    import subprocess
    src = ['import LeanTheory.Theory.Life.LayoutPieces',
           'open LeanTheory.Computability LeanTheory.Life.LP',
           'def progs : List (String × Program) := [' + ', '.join(
               '("%s", [%s])' % (nm, ', '.join(LEAN_PROG[ins[0]](ins) for ins in pr))
               for nm, pr in progs.items()) + ']',
           'def main : IO Unit := do',
           '  for (n, p) in progs do',
           '    for s in machSpecs p do',
           '      IO.println s!"{n} {reprStr s.base} {s.vx} {s.vy} {s.ph}"',
           '#eval main']
    path = os.path.join(tmpdir, 'layout_pieces_eval.lean')
    open(path, 'w').write('\n'.join(src) + '\n')
    out = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
    res = {nm: [] for nm in progs}
    for line in out.stdout.splitlines():
        m = re.match(r'(\w+) LeanTheory\.Life\.LP\.Base\.(\w+)(?: (\d+))? (-?\d+) (-?\d+) (\d+)$', line)
        assert m, line
        nmb = BASE_NAME[m.group(2)]
        if '%s' in nmb:
            nmb = nmb % m.group(3)
        res[m.group(1)].append((nmb, int(m.group(4)), int(m.group(5)), int(m.group(6))))
    return res


def main():
    args = sys.argv[1:]
    tmp, sweep = None, 0
    if '--lean' in args:
        i = args.index('--lean')
        tmp = args[i + 1]
        args = args[:i] + args[i + 2:]
    if '--sweep' in args:
        i = args.index('--sweep')
        sweep = int(args[i + 1])
        args = args[:i] + args[i + 2:]
    names = args or ['add', 'share', 'rand']
    progs = {nm: [tuple(x) for x in p1_layout.get_prog(nm)] for nm in names}
    if sweep:
        import random
        import p5_formulas
        rng = random.Random(11)
        for n in range(sweep):
            progs['sweep%d' % n] = p5_formulas.rand_prog(rng)
    print('bases:')
    ok = check_bases(lean_bases())
    for nm, pr in progs.items():
        ok &= compare(nm, pr)
    if tmp:
        ev = lean_eval(progs, tmp)
        for nm, pr in progs.items():
            _, py = machPieces(pr)
            same = ev[nm] == py
            ok &= same
            print('%s: Lean evaluation of LP.machSpecs (%d specs) = this re-implementation: %s' % (
                nm, len(ev[nm]), same))
    print('ALL AGREE' if ok else 'DISAGREEMENT')


if __name__ == '__main__':
    main()
