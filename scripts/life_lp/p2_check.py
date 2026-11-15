#!/usr/bin/env python3
"""P2 (R-31): checks of the provable layout LP(program) (no simulation).

(F) the separation inequalities of R-31 §3 evaluated from the formulas (pair class -> margin);
(S) segment level, in (u, v): every route corner (reflector) vs every foreign route segment that
    spans it: perpendicular gap >= 60 (the reflector envelope reaches 23, a glider 2);
(C) cell level: every piece envelope / eater vs every route segment it does not interact with
    >= 13 cells (Chebyshev; conservative bound (|du| + |dv|) / 2 for the glider strip);
    pieces of different groups >= 13 cells; HALT cell >= 300 cells from every piece and segment
    other than the HALT line;
(D) register diagonals u = U_r - 96, v >= 404: no foreign piece, eater or segment within 60 in u
    (any v: for every k), and B_-1 .. B_600 cell distance >= 13;
(T) timing: residues at every window input, token deltas, continue and Z-answer slacks, the delay
    formulas of §4 against the values found by building the routes;
(X) concurrency: crossings of concurrent links (decJz: KNZ, C, KZ; and KZ with the NZ answer, KNZ
    with the Z answer; inc: continue, link, merge) with the time difference at the crossing.
Usage: p2_check.py PROGRAM      (results/p2_<program>.txt)"""
import sys
from lpcommon import *
from net import rf_point
import p1_layout as P1

MARG_S, MARG_C = 60, 13


def segments(m, L):
    """[(leg index, glider, 'u'|'v', coordinate, lo, hi)] in (u, v)."""
    cor = L['corners']
    legs = L['legs']
    out = []
    for k, g in enumerate(legs):
        typ = 'u' if is_u(g[0]) else 'v'
        c = coord_of(g)
        ends = []
        if k > 0:
            p = cor[k - 1]
            ends.append(p[1] if typ == 'u' else p[0])
        if k < len(cor):
            p = cor[k]
            ends.append(p[1] if typ == 'u' else p[0])
        else:
            if L.get('gate') is not None:
                cx, cy = cross(L['gate'])
                q = (cx - cy, cx + cy)
                ends.append(q[1] if typ == 'u' else q[0])
            elif L['dst'][0] == 'halt':
                ends.append(m.halt_cell_uv[0] - 1000)
            else:                                     # token: up to the station gate (module frame)
                ends.append(ends[-1] + (-700 if g[0] in (NW, SW) else 700))
        if k == 0:
            s = L['src']
            if s[0] == 'unit':
                d = m.UN[s[1]]
                start = m.const['V_U'] + d['T'].uvbox[3]
                ends.insert(0, start)
            else:                                     # answers start at their station
                ends.insert(0, ends[0] + (400 if g[0] in (NW, SW) else -400))
        out.append((k, g, typ, c, min(ends), max(ends)))
    return out


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'add'
    prog = [tuple(x) for x in P1.get_prog(name)]
    m = P1.layout(prog)
    out = open(os.path.join(LPRES, 'p2_%s.txt' % name), 'w')

    def log(s=''):
        print(s, flush=True)
        out.write(s + '\n')
    P1.describe(m, log)
    c = m.const
    N, R, D, P = m.N, m.R, m.D, m.P
    fails = 0
    # ---------------- (F) formula-level inequalities ----------------------------------------
    log('\n(F) separation inequalities (formulas; margin = left side - right side)')
    ub = m.M['uvbox']
    ext = m.M['ext']
    rows = []
    rows.append(('unit slab a vs a+1: A_a + right <= A_{a+1} + left - 60', c['P_U'] - (c['slab'][1] - c['slab'][0]) - 60))
    rows.append(('unit row bottom vs band top: V_U + 1523 <= V_T - 120', c['V_T'] - 120 - (c['V_U'] + 1523)))
    rows.append(('band bottom vs module top: V_T + 660 NB <= -3324 - 198 D - 120', -3324 - 198 * D - 120 - (c['V_T'] + 660 * c['NB'])))
    rows.append(('sub-band b: its tracks (V_T + 660 b + [0, 559]) vs sub-band b + 1', 660 - 559 - 60))
    rows.append(('tracks of one sub-band: |62 s - 62 s\'| - 1 (parity) >= 60', 62 - 1 - 60))
    rows.append(('last unit slab vs zone of module 0: A_{N+R-1} + right + 120 <= U_0 + ext_left',
                 c['U_0'] + ext[0] - (m.A[-1] + c['slab'][1] + 120)))
    rows.append(('module r vs r+1 (with zones): U_r + ext_right + 60 <= U_{r+1} + ext_left', c['P_M'] - (ext[2] - ext[0]) - 60))
    rows.append(('regular hairpins vs unit 0: H_I + 360 <= A_0 + left - 120', c['A_0'] + c['slab'][0] - 120 - (c['H_I'] + 360)))
    rows.append(('diagonal vs left zone: U_r + uL <= U_r - 96 - 60', -96 - 60 - (ub[0] - 60)))
    rows.append(('diagonal vs right-zone legs (u >= U_r + 1230): U_r - 96 + 60 <= U_r + 1230', 1230 - (-96 + 60)))
    rows.append(('diagonal of r+1 vs right zone of r: U_r + ext_right <= U_{r+1} - 96 - 60', c['P_M'] - 96 - 60 - ext[2]))
    for nm, mg in rows:
        log('  %-95s margin %d %s' % (nm, mg, '' if mg >= 0 else 'FAIL'))
        fails += mg < 0
    # columns, tracks, hairpins distinct
    cols = {}
    for L in m.links:
        for k, g, typ, cc, lo, hi in segments(m, L):
            pass
    # ---------------- segments ---------------------------------------------------------------
    SEG = []                                   # (link name, k, g, typ, c, lo, hi)
    for L in m.links:
        for k, g, typ, cc, lo, hi in segments(m, L):
            SEG.append((L['name'], k, g, typ, cc, lo, hi))
    # (S) corners vs foreign segments
    worst = 10 ** 9
    nS = 0
    for L in m.links:
        for idx, (cu, cv) in enumerate(L['corners']):
            for (ln, k, g, typ, cc, lo, hi) in SEG:
                if ln == L['name'] and k in (idx, idx + 1):
                    continue
                if typ == 'u':
                    if lo - 30 <= cv <= hi + 30:
                        gap = abs(cu - cc)
                    else:
                        continue
                else:
                    if lo - 30 <= cu <= hi + 30:
                        gap = abs(cv - cc)
                    else:
                        continue
                worst = min(worst, gap)
                if gap < MARG_S:
                    nS += 1
                    if nS < 20:
                        log('  (S) FAIL corner %s #%d (%d, %d) - segment %s leg %d %s %d [%d, %d]: gap %d' % (
                            L['name'], idx, cu, cv, ln, k, typ, cc, lo, hi, gap))
    log('(S) route corners vs foreign segments spanning them: min perpendicular gap %d (>= %d required), failures %d' % (worst, MARG_S, nS))
    fails += nS
    # ---------------- (C) cell level ---------------------------------------------------------
    envs = [env_cells(p) for p in m.pieces]
    own_of = {}
    for i, nmg in enumerate(m.names):
        own_of.setdefault(nmg, []).append(i)
    arrs = []
    for e in envs:
        a = [(x - y, x + y) for x, y in e]
        arrs.append(a)
    eat = [(x - y, x + y) for x, y in m.eaters]
    boxes = [(min(p[0] for p in a), min(p[1] for p in a), max(p[0] for p in a), max(p[1] for p in a)) for a in arrs]

    def group(nmg):
        return nmg[:2] if nmg[0] in ('M', 'U') else ('R', nmg[1])

    def segdist(a, typ, cc, lo, hi):
        if typ == 'u':
            return min((max(0, abs(u - cc) - 2) + max(0, lo - 4 - v, v - hi - 4)) // 2 for u, v in a)
        return min((max(0, lo - 4 - u, u - hi - 4) + max(0, abs(v - cc) - 2)) // 2 for u, v in a)
    worst = 10 ** 9
    nC = 0
    byname = m.byname
    for (ln, k, g, typ, cc, lo, hi) in SEG:
        L = byname[ln]
        nlegs = len(L['legs'])
        for i, a in enumerate(arrs):
            b = boxes[i]
            if typ == 'u':
                bd = max(0, b[0] - cc - 2, cc - 2 - b[2]) + max(0, lo - 4 - b[3], b[1] - hi - 4)
            else:
                bd = max(0, b[1] - cc - 2, cc - 2 - b[3]) + max(0, lo - 4 - b[2], b[0] - hi - 4)
            if bd // 2 >= MARG_C:
                continue
            gname = m.names[i]
            # interacting pieces: own corners; the source unit (leg 0); the destination unit/module
            if gname[0] == 'R' and gname[1] == ln:
                continue
            s, dd = L['src'], L['dst']
            if k == 0 and s[0] == 'unit' and gname == ('U', s[1]):
                continue
            if k <= 1 and s[0] == 'ans' and gname == ('M', s[1]):
                continue
            if k == nlegs - 1 and dd[0] == 'unit' and gname == ('U', dd[1]):
                continue
            if k >= nlegs - 3 and dd[0] == 'port' and gname == ('M', dd[1]):
                continue
            d = segdist(a, typ, cc, lo, hi)
            if d < MARG_C:
                nC += 1
                if nC < 30:
                    log('  (C) FAIL %s leg %d (%s %d [%d, %d]) - piece %s %s: %d' % (ln, k, typ, cc, lo, hi, gname, m.pieces[i], d))
            worst = min(worst, d)
        # eaters: only the module's own port legs may come near
        if len(eat):
            d = segdist(eat, typ, cc, lo, hi)
            near_mod = (k >= nlegs - 3 and L['dst'][0] == 'port') or (k <= 1 and L['src'][0] == 'ans')
            if d < MARG_C and not near_mod:
                nC += 1
                log('  (C) FAIL %s leg %d - eater: %d' % (ln, k, d))
    log('(C) route segments vs pieces they do not interact with: min cell distance %d (>= %d), failures %d' % (worst, MARG_C, nC))
    fails += nC
    # pieces of different groups
    worst, nG = 10 ** 9, 0
    G = [group(n) for n in m.names]
    for i in range(len(arrs)):
        for j in range(i):
            if G[i] == G[j]:
                continue
            bi, bj = boxes[i], boxes[j]
            bd = (max(0, bi[0] - bj[2], bj[0] - bi[2]) + max(0, bi[1] - bj[3], bj[1] - bi[3])) // 2
            if bd >= 40:
                continue
            d = set_dist(envs[i], envs[j])
            worst = min(worst, d)
            if d < MARG_C:
                nG += 1
                log('  (C) FAIL pieces %s %s / %s %s: %d' % (m.names[i], m.pieces[i], m.names[j], m.pieces[j], d))
    log('(C) piece envelopes of different groups (unit, module, route link): min cell distance %s (box < 40), failures %d' % (worst, nG))
    fails += nG
    # HALT cell
    hu, hv = m.halt_cell_uv
    hp = [(hu, hv)]
    dmin = min(min((abs(u - hu) + abs(v - hv)) // 2 for u, v in a) for a in arrs)
    dseg = min(segdist(hp, typ, cc, lo, hi) for (ln, k, g, typ, cc, lo, hi) in SEG if not ln.startswith('halt'))
    log('(C) HALT cell (u, v) = %s, xy %s: distance to every piece %d, to every other route segment %d; the halt glider passes it' % (
        m.halt_cell_uv, xy(hu, hv), dmin, dseg))
    fails += dmin < 300 or dseg < 300
    # ---------------- (D) diagonals ----------------------------------------------------------
    nD = 0
    for r in range(R):
        ud = m.U[r] - 96
        for i, a in enumerate(arrs):
            if m.names[i] == ('M', r):
                continue
            sel = [p for p in a if p[1] >= 404 - 60]
            if sel and min(abs(p[0] - ud) for p in sel) < 60:
                nD += 1
                log('  (D) FAIL diagonal %d - piece %s' % (r, m.names[i]))
        for (ln, k, g, typ, cc, lo, hi) in SEG:
            if typ == 'u' and abs(cc - ud) < 60 and hi >= 404 - 60:
                nD += 1
                log('  (D) FAIL diagonal %d - %s leg %d' % (r, ln, k))
            if typ == 'v' and cc >= 404 - 60 and lo - 60 <= ud <= hi + 60:
                nD += 1
                log('  (D) FAIL diagonal %d - %s leg %d (crosses)' % (r, ln, k))
        B = translate(blocks(-1, 600), m.U[r] // 2, -m.U[r] // 2)
        for i, a in enumerate(arrs):
            if m.names[i] == ('M', r):
                continue
            if boxes[i][3] < 300 or abs((boxes[i][0] + boxes[i][2]) / 2 - ud) > 400:
                continue
            d = set_dist(envs[i], B)
            if d < MARG_C:
                nD += 1
                log('  (D) FAIL B_k of %d - piece %s: %d' % (r, m.names[i], d))
    log('(D) register diagonals (u = U_r - 96, v >= 404, every k): foreign pieces / segments within 60 in u: failures %d' % nD)
    fails += nD
    # ---------------- (T) timing -------------------------------------------------------------
    log('\n(T) timing')
    for L in m.links:
        if 'rho' in L and L['kind'] != 'C':
            g = L['final']
            res = (g[2] - L['wlo'][2]) % 30
            ok = res == L['rho']
            fails += not ok
            log('  %-10s %-5s arrival residue %2d (window tau..tau+12; rho* = %d) e = 2 (rho* - r0) mod 15 = %2d (r0 = %2d) %s' % (
                L['name'], L['kind'], res, L['rho'], L['e'], L['r0'], 'ok' if ok else 'FAIL'))
    for i, ins in enumerate(prog):
        if ins[0] != 'dec':
            continue
        LC, LN, LZ = byname['dec%d.C' % i], byname['dec%d.KNZ' % i], byname['dec%d.KZ' % i]
        j = LC['j']
        q = D - 1 - j
        eC_f = (9 * q) % 15
        dN0_f = -3936 - 228 * q
        dZ0_f = 367 + 1564 * q - 8 * eC_f
        sg_f = 2 * (q % 2)
        x_f = max(0, -(-(dZ0_f - 30 * sg_f + 1) // 120))
        eKZ_f = (-1 - dZ0_f + 30 * sg_f + 120 * x_f) // 8
        EN_f = (-dN0_f - 2 * sg_f) // 8
        got = (LC['eC'], LC['dN0'], LC['dZ0'], LC['sigma'], LC['x'], LZ['e'], LN['e'])
        want = (eC_f, dN0_f, dZ0_f, sg_f, x_f, eKZ_f, EN_f)
        ok = got == want
        fails += not ok
        res = (LC['final'][2] - LC['wlo'][2]) % 30
        log('  dec%d (r %d, j %d, q %d, D %d): C residue %d = 4 + 2 sigma; (e_C, dN0, dZ0, sigma, x, e_KZ, E_N) = %s; formulas %s %s; '
            'token deltas KNZ %d, KZ %d' % (i, ins[1], j, q, D, res, got, want, 'ok' if ok else 'FAIL', LN['delta'], LZ['delta']))
    for L in m.links:
        if L['kind'] in ('cont', 'Z'):
            ok = L['slack'] >= 0
            fails += not ok
            what = 'continue at its up-turn corner - (INC control at the INC gate + 500)' if L['kind'] == 'cont' else \
                'Z answer at its gate - (DZ2 Z restore end + 300)'
            log('  %-10s %s = %d %s' % (L['name'], what, L['slack'], 'ok' if ok else 'FAIL'))
    # unpaired tokens: consumed before the next instruction starts / the answer leaves
    for i, ins in enumerate(prog):
        if ins[0] != 'dec':
            continue
        LZ, LN, Ln, Lz = byname['dec%d.KZ' % i], byname['dec%d.KNZ' % i], byname['dec%d.nz' % i], byname['dec%d.z' % i]
        r, j = ins[1], LZ['j']
        st = m.M['stations']
        gz = move(st['z'][j][0], m.U[r] // 2, -m.U[r] // 2)
        gn = move(st['nz'][j][0], m.U[r] // 2, -m.U[r] // 2)
        rz = move(st['z'][j][1], m.U[r] // 2, -m.U[r] // 2)
        tZ = time_at(LZ['target'], cross(gz))
        tn = time_at(Ln['final'], cross(Ln['gate']))
        tN = time_at(LN['target'], cross(gn))
        tz0 = time_at(Lz['g0'], rf_point(rz))
        log('  dec%d: unpaired Z token (NZ case) at its station gate %d generations before the NZ answer reaches unit %d; '
            'unpaired NZ token (Z case) at its station gate %d generations before the Z answer leaves its station' % (
                i, tn - tZ, i + 1, tz0 - tN))
        fails += (tn - tZ) < 1000 or (tz0 - tN) < 0
    # ---------------- (X) concurrency --------------------------------------------------------
    log('\n(X) crossings of concurrent links (time difference at the crossing point)')
    groups = []
    for i, ins in enumerate(prog):
        if ins[0] == 'dec':
            groups.append(('dec%d bundle' % i, ['dec%d.%s' % (i, o) for o in ('KNZ', 'C', 'KZ')]))
            groups.append(('dec%d KZ / NZ answer' % i, ['dec%d.KZ' % i, 'dec%d.nz' % i]))
            groups.append(('dec%d KNZ / Z answer' % i, ['dec%d.KNZ' % i, 'dec%d.z' % i]))
        elif ins[0] == 'inc':
            groups.append(('inc%d' % i, ['inc%d.cont' % i, 'inc%d.link' % i, 'merge%d@%d' % (ins[1], i)]))
    segL = {}
    for L in m.links:
        segL[L['name']] = segments(m, L)
    for i, ins in enumerate(prog):
        if ins[0] == 'inc':
            Ll = byname['inc%d.link' % i]
            Lm = dict(byname['merge%d' % ins[1]])
            Lm['legs'] = Ll['merge_legs']
            segL['merge%d@%d' % (ins[1], i)] = segments(m, Lm)
    nX = 0
    for gname, members in groups:
        found = []
        for a in range(len(members)):
            for b in range(a):
                for (k1, g1, t1, c1, lo1, hi1) in segL[members[a]]:
                    for (k2, g2, t2, c2, lo2, hi2) in segL[members[b]]:
                        if t1 == t2:
                            if abs(c1 - c2) < MARG_S and not (hi1 < lo2 or hi2 < lo1):
                                found.append((members[a], members[b], 'parallel', c1, c2, None))
                            continue
                        if lo2 - 6 <= c1 <= hi2 + 6 and lo1 - 6 <= c2 <= hi1 + 6:
                            uu, vv = (c1, c2) if t1 == 'u' else (c2, c1)
                            dt = tuv(g1, uu, vv) - tuv(g2, uu, vv)
                            found.append((members[a], members[b], (uu, vv), k1, k2, dt))
        if not found:
            log('  %-22s: no crossing' % gname)
        for f in found:
            bad = f[2] == 'parallel' or abs(f[5]) < 500
            nX += bad
            log('  %-22s: %s leg %s x %s leg %s at (u, v) %s: dt %s %s' % (gname, f[0], f[3], f[1], f[4], f[2], f[5], 'FAIL' if bad else ''))
    fails += nX
    log('\nTOTAL failures: %d' % fails)


if __name__ == '__main__':
    main()
