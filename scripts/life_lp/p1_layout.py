#!/usr/bin/env python3
"""P1 (R-31): the provable layout rule LP(program).  Every position is a closed formula (affine in the
indices, with parity / residue corrections given by explicit mod formulas); see R-31 §2.

Program: list of ('inc', r) | ('dec', r, z) | ('halt',), exactly one 'halt' (normal form).
Indices: instruction i in [0, N), register r in [0, R) (R = 1 + max register), caller index j of a
decJz on its register (j < D), copy index t of an entry chain (t < 2P), link index k (< K).

GLOBAL PARAMETERS (computed from the program):
  N, R, D = max(1, max_r #decJz on r), P = max(1, max #predecessors of a unit), K = 2 + 5N + R.
CONSTANTS (multiples of 30 where they enter timing):
  unit pitch  P_U = 540 + 180 P          unit a at u = A_a = A_0 + P_U a  (a < N: instruction a,
                                          a = N + r: merge unit of register r), v = V_U
  module pitch P_M = 2400 + 540 D        module r at u-shift U_r = U_0 + P_M r, v-shift 0
  tracks      OUT_k = V_T + 60 k + pi_k,  BACK_k = V_T + 60 (2K - k) + pi_k  (mirror: nesting)
  hairpins    H_k = H_I + 90 k - 2 e_k - sigma_k  (- G_far for the INC continues)
"""
import sys
import json
from lpcommon import *
import p0_parts

TOK_W = [-3, -1, 0, 1, 2, 7, 8, 9]       # R-29 §2.3: accepted token delays


def fixp(c, p):
    """c or c - 1 with parity p."""
    return c if (c - p) % 2 == 0 else c - 1


class LP:
    pass


def analyse(prog):
    N = len(prog)
    halts = [i for i, ins in enumerate(prog) if ins[0] == 'halt']
    assert len(halts) == 1, 'normal form: exactly one halt'
    R = 1 + max(ins[1] for ins in prog if ins[0] != 'halt')
    decs = {r: [i for i, ins in enumerate(prog) if ins[0] == 'dec' and ins[1] == r] for r in range(R)}
    incs = {r: [i for i, ins in enumerate(prog) if ins[0] == 'inc' and ins[1] == r] for r in range(R)}
    preds = {a: [] for a in range(N + R)}
    preds[0].append(('start',))
    for i, ins in enumerate(prog):
        if ins[0] == 'inc':
            preds[i + 1].append(('cont', i))
            preds[N + ins[1]].append(('link', i))
        elif ins[0] == 'dec':
            preds[i + 1].append(('nz', i))
            preds[ins[2]].append(('z', i))
    D = max([1] + [len(v) for v in decs.values()])
    P = max([1] + [len(v) for v in preds.values()])
    return N, R, D, P, decs, incs, preds, halts[0]


B_Z = 1500


def module_frame(D):
    """Module M(D) data in its own frame (module 0 at the origin) + zone formulas (§2.3).
    Right zone (q = D - 1 - j): Z answer j turns at v_d = B_Z + 180 q, Z token j at w_d = v_d + 61."""
    M = L2.mod(D)
    ub = M['uvbox']                      # (-733, -3324 - 198 D, 1350 + 144 D, 1379 + 144 D)
    assert ub == (-733, -3324 - 198 * D, 1350 + 144 * D, 1379 + 144 * D), ub
    Z = {}
    uL, uR = ub[0] - 60, ub[2] + 60      # zone edges
    # left zone: idx 0 .. 4D, channel c = uL - 62 idx - pi (pi: parity of the port corner)
    for t in range(2 * D):
        v = coord_of(M['dec'][t])
        Z['dec%d' % t] = (fixp(uL - 62 * t, 1 - v % 2), v)
    v = coord_of(M['inc'][0])
    Z['inc'] = (fixp(uL - 62 * 2 * D, 1 - v % 2), v)
    for j in range(D):
        v = coord_of(M['nz'][j][0])
        Z['nztok%d' % j] = (fixp(uL - 62 * (2 * D + 1 + 2 * j), 1 - v % 2), v)
        v = coord_of(M['nz'][j][1])
        Z['nzret%d' % j] = (fixp(uL - 62 * (2 * D + 2 + 2 * j), 1 - v % 2), v)
    # right zone: q = D - 1 - j; Z answer turns NE at v_d, Z token turns SW at w_d = v_d + 61
    for j in range(D):
        q = D - 1 - j
        uz = coord_of(M['z'][j][1])            # SE line of the dispatched Z answer
        uk = coord_of(M['z'][j][0])            # NW line of the Z token
        vd = fixp(B_Z + 180 * q, 1 - uz % 2)          # below the Z stations (v <= 681)
        wd = vd + 61
        assert (wd + uk) % 2 == 1
        cz = fixp(uR + 124 * q, 1 - vd % 2)
        ck = fixp(uR + 124 * q + 62, 1 - wd % 2)
        Z['zret%d' % j] = (cz, vd, uz)
        Z['ztok%d' % j] = (ck, wd, uk)
    M['zone'] = Z
    M['ext'] = (uL - 62 * 4 * D - 30, ub[1], uR + 124 * (D - 1) + 92, max(ub[3], B_Z + 180 * (D - 1) + 61) + 30)
    return M


def layout(prog, delays=None, probe=False):
    """delays: dict overriding the delay formulas (G_far); probe: record dt0 /
    slack values instead of failing."""
    N, R, D, P, decs, incs, preds, ih = analyse(prog)
    m = LP()
    m.prog, m.N, m.R, m.D, m.P = prog, N, R, D, P
    m.decs, m.incs, m.preds = decs, incs, preds
    n = 2 * P
    T = {kind: p0_parts.unit(kind, n) for kind in ('dec', 'inc', 'halt', 'merge')}
    m.T = T
    # ---------------- constants (section 2 of R-31) -------------------------------------------
    P_U = 540 + 180 * P
    P_M = 2400 + 540 * D
    slab_left = min(t.left for t in T.values())          # = -206 - 122 P (dec)
    slab_right = max(t.right for t in T.values())        # = max(238, 86 + 58 P)
    assert slab_left == -206 - 122 * P and slab_right == max(238, 86 + 58 * P), (slab_left, slab_right)
    A_0 = 0
    NB = 2 + N + R                                       # sub-bands: halt, instructions, merges
    V_T = -30 * -(-(3324 + 198 * D + 120 + 660 * NB) // 30)   # band top, = 0 mod 30; band = [V_T, V_T + 660 NB)
    V_U = V_T - 1644                                     # unit origin row (even)
    U_0 = 30 * -(-(P_U * (N + R - 1) + slab_right + 120 + 823 + 248 * D) // 30)
    H_I = 30 * ((A_0 + slab_left - 510) // 30)          # = 0 mod 30; regular hairpins: H_I + 90 s - 2 e (s <= 4)
    dl = delay_formulas(N, R, D, P, P_U, P_M, U_0, H_I)
    if delays:
        dl.update(delays)
    m.delays = dl
    M = module_frame(D)
    m.M = M
    m.const = dict(P_U=P_U, P_M=P_M, A_0=A_0, V_U=V_U, V_T=V_T, U_0=U_0, H_I=H_I, NB=NB,
                   slab=(slab_left, slab_right), G_far=dl['G_far'])
    A = [A_0 + P_U * a for a in range(N + R)]
    U = [U_0 + P_M * r for r in range(R)]
    m.A, m.U = A, U
    pieces, names, eaters = [], [], set()

    def add(p, name):
        pieces.append(p)
        names.append(name)

    # ---------------- modules ---------------------------------------------------------------
    def W(w, r):
        return mwl(w, U[r] // 2, -U[r] // 2)
    for r in range(R):
        for p in M['pieces']:
            add(move(p, U[r] // 2, -U[r] // 2), ('M', r))
        eaters |= set(translate(M['eaters'], U[r] // 2, -U[r] // 2))
    # ---------------- units -----------------------------------------------------------------
    kinds = [('halt' if ins[0] == 'halt' else ins[0]) for ins in prog] + ['merge'] * R
    m.kinds = kinds
    UN = []
    for a in range(N + R):
        Tm = T[kinds[a]]
        dxy = ((A[a] + V_U) // 2, (V_U - A[a]) // 2)
        d = {'T': Tm, 'dxy': dxy, 'kind': kinds[a]}
        d['gates'] = [move(g, *dxy) for g in Tm.gates]
        d['side'] = [mwl(w, *dxy) for w in Tm.side]
        d['in_cols'] = [A[a] + c for c in Tm.in_cols]
        d['v_side'] = [V_U + v for v in Tm.v_side]
        d['io'] = [{k: mwl(w, *dxy) for k, w in io.items()} for io in Tm.io]
        d['copy'] = {}
        d['used'] = not (a >= N and not incs[a - N])
        if d['used']:
            for p in Tm.pieces:
                add(move(p, *dxy), ('U', a))
        UN.append(d)
    m.UN = UN

    def copy_for(a, pred, src_par):
        """predecessor number e of unit a uses copy t = 2 e + b (b: parity of the source column)."""
        e = preds[a].index(pred)
        for t in (2 * e, 2 * e + 1):
            if UN[a]['in_cols'][t] % 2 == src_par % 2:
                UN[a]['copy'][pred] = t
                return t
        raise AssertionError
    # ---------------- links: (sub-band b, slot s) -------------------------------------------
    links = []

    def L_(**kw):
        links.append(kw)
        return kw
    for i, ins in enumerate(prog):
        b = 1 + i
        if ins[0] == 'inc':
            r = ins[1]
            L_(name='inc%d.cont' % i, b=b, s=0, src=('unit', i, 'D'), dst=('unit', i + 1, ('cont', i)), act=i, kind='cont')
            L_(name='inc%d.link' % i, b=b, s=1, src=('unit', i, 'R'), dst=('unit', N + r, ('link', i)), act=i, kind='link')
        elif ins[0] == 'dec':
            r = ins[1]
            j = decs[r].index(i)
            L_(name='dec%d.KNZ' % i, b=b, s=0, src=('unit', i, 'L'), dst=('port', r, 'nztok%d' % j), act=i, j=j, kind='KNZ')
            L_(name='dec%d.C' % i, b=b, s=1, src=('unit', i, 'R'), dst=('port', r, 'dec%d' % (2 * j)), act=i, j=j, kind='C')
            L_(name='dec%d.KZ' % i, b=b, s=2, src=('unit', i, 'D'), dst=('port', r, 'ztok%d' % j), act=i, j=j, kind='KZ')
            L_(name='dec%d.nz' % i, b=b, s=3, src=('ans', r, 'nz', j, i), dst=('unit', i + 1, ('nz', i)), act=('nz', i), j=j, kind='NZ')
            L_(name='dec%d.z' % i, b=b, s=4, src=('ans', r, 'z', j, i), dst=('unit', ins[2], ('z', i)), act=('z', i), j=j, kind='Z')
        else:
            L_(name='halt%d' % i, b=0, s=0, src=('unit', i, 'D'), dst=('halt',), act=i, kind='halt')
    for r in range(R):
        if incs[r]:
            L_(name='merge%d' % r, b=1 + N + r, s=0, src=('unit', N + r, 'D'), dst=('port', r, 'inc'), act=('M', r), kind='merge')
    byname = {L['name']: L for L in links}
    m.links, m.byname = links, byname
    Zn = M['zone']
    for L in links:
        s = L['src']
        if s[0] == 'unit':
            a, o = s[1], s[2]
            L['g0'] = UN[a]['io'][0][o]
            L['csrc'] = coord_of(L['g0'])
            L['prefix'] = []
        else:
            _, r, which, j, i = s
            if which == 'nz':
                c = Zn['nzret%d' % j][0] + U[r]
                L['prefix'] = [(NW, c)]
            else:
                cz, vd, uz = Zn['zret%d' % j]
                c = cz + U[r]
                L['prefix'] = [(NE, vd), (NW, c)]
            L['csrc'] = c
        p_s = L['csrc'] % 2
        L['OUT'] = V_T + 660 * L['b'] + 62 * L['s'] + (1 - p_s)          # pi = 1 - p_s (V_T even)
        L['BACK'] = V_T + 660 * L['b'] + 62 * (9 - L['s']) + (1 - p_s)
        dd = L['dst']
        if dd[0] == 'unit':
            a = dd[1]
            t = copy_for(a, dd[2], p_s)
            L['t'] = t
            L['cdst'] = UN[a]['in_cols'][t]
            L['suffix'] = [(NW, L['cdst']), (NE, UN[a]['v_side'][t])]
            L['wlo'] = UN[a]['side'][t]
            L['gate'] = UN[a]['gates'][t]
        elif dd[0] == 'port':
            _, r, nm = dd
            z = Zn[nm]
            L['cdst'] = z[0] + U[r]
            if nm.startswith('ztok'):
                L['suffix'] = [(SE, L['cdst']), (SW, z[1]), (NW, z[2] + U[r])]
            else:
                L['suffix'] = [(SE, L['cdst']), (NE, z[1])]
            L['gate'] = None
            if nm.startswith('dec'):
                tt = int(nm[3:])
                L['wlo'] = W(M['dec'][tt], r)
                L['gate'] = move(M['dec_gates'][tt], U[r] // 2, -U[r] // 2)
                L['cprime'] = (W(M['cprime'][tt][0], r), W(M['cprime'][tt][1], r))
            elif nm == 'inc':
                L['wlo'] = W(M['inc'][0], r)
                L['gate'] = move(M['inc_gates'][0], U[r] // 2, -U[r] // 2)
            assert L['cdst'] % 2 == p_s, (L['name'], L['cdst'], p_s)
        else:
            L['cdst'] = None
            L['suffix'] = []

    def gfar(L):
        """G_far(i) = 30 ceil(max(0, T_INC + 500 - T_corner^0) / 120) (section 4.3): set in step 3."""
        return L.get('G', 0)

    def hair(L, e):
        """H = H_I + 90 s - 2 e - X: X = 62 + G_far for the INC continue; the KNZ hairpin is placed
        relative to C's: H_KNZ = H_C - 62 - 2 E_N (L['e'] = E_N)."""
        if L['kind'] == 'KNZ':
            LC = byname[L['name'][:-3] + 'C']
            return fixp(hair(LC, LC['e']) - 62 - 2 * e, L['csrc'] % 2)
        X = 62 + gfar(L) if L['kind'] == 'cont' else 0
        return fixp(H_I + 90 * L['s'] - 2 * e - X, L['csrc'] % 2)

    def build(L, e, g0=None):
        g0 = L['g0'] if g0 is None else g0
        if L['dst'][0] == 'halt':
            return route(g0, [(SW, L['OUT'])])
        turns = L['prefix'] + [(SW, L['OUT']), (SE, hair(L, e)), (NE, L['BACK'])] + L['suffix']
        return route(g0, turns)

    def window_res(L, g):
        assert g[:2] == L['wlo'][:2], (L['name'], g, L['wlo'])
        return (g[2] - L['wlo'][2]) % 30

    def solve_window(L, g0=None):
        """e = 2 (rho* - r0) mod 15 (r0: residue for e = 0; rho* = 4 or 5, the one of r0's parity)."""
        pcs, g, cor, legs = build(L, 0, g0)
        r0 = window_res(L, g)
        rho = 4 if r0 % 2 == 0 else 5
        e = (2 * (rho - r0)) % 15
        pcs, g, cor, legs = build(L, e, g0)
        assert window_res(L, g) == rho, (L['name'], r0, e, window_res(L, g))
        L['e'], L['r0'], L['rho'] = e, r0, rho
        return pcs, g, cor, legs

    def slot(L, g):
        return (g[2] - L['wlo'][2]) // 30

    sol = {}
    m.probe = []
    # 1. decJz bundles (R-31 section 4.2): C at residue rho* + 2 sigma, slot shifted by x; tokens exact
    def token_dt(LT, j, r, cp):
        nm = 'nz' if LT['kind'] == 'KNZ' else 'z'
        target = mwl(W(M[nm][j][0], r), 0, 0, cp[2] - W(M['CP'], r)[2])
        pcs, g2, c2, l2 = build(LT, LT['e'])
        assert g2[:2] == target[:2]
        return g2[2] - target[2], target, (pcs, g2, c2, l2)

    def c_prime(LC, g):
        w_in, cp = LC['cprime']
        return mwl(cp, 0, 0, 30 * (slot(LC, g) - slot(LC, w_in)))
    for i, ins in enumerate(prog):
        if ins[0] != 'dec':
            continue
        r = ins[1]
        j = decs[r].index(i)
        LC, LN, LZ = byname['dec%d.C' % i], byname['dec%d.KNZ' % i], byname['dec%d.KZ' % i]
        solve_window(LC)
        eC = LC['e']
        LN['e'] = LZ['e'] = 0
        cp = c_prime(LC, build(LC, eC)[1])
        dN0, _, _ = token_dt(LN, j, r, cp)
        dZ0, _, _ = token_dt(LZ, j, r, cp)
        # sigma: 30 sigma fixes the classes mod 8 (KNZ -> 0, KZ -> 7)
        sig = [sg for sg in (0, 1, 2) if (dN0 - 30 * sg) % 8 == 0 and (dZ0 - 30 * sg) % 8 == 7]
        assert sig, (LC['name'], dN0 % 8, dZ0 % 8)
        sg = sig[0]
        x = max(0, -(-(dZ0 - 30 * sg + 1) // 120))
        LC['e'] = eC + 4 * sg + 15 * x
        LC['sigma'], LC['x'], LC['eC'], LC['dN0'], LC['dZ0'] = sg, x, eC, dN0, dZ0
        sol[LC['name']] = build(LC, LC['e'])
        g = sol[LC['name']][1]
        assert window_res(LC, g) == LC['rho'] + 2 * sg
        cp = c_prime(LC, g)
        LC['Cp'] = cp
        LN['e'] = LZ['e'] = 0
        dN, _, _ = token_dt(LN, j, r, cp)
        dZ, _, _ = token_dt(LZ, j, r, cp)
        assert dN <= 0 and dN % 8 == 0 and -113 <= dZ <= -1 and dZ % 8 == 7, (LC['name'], dN, dZ)
        LN['e'] = -dN // 8
        LZ['e'] = (-1 - dZ) // 8
        for LT, want in ((LN, 0), (LZ, -1)):
            dt, target, sl = token_dt(LT, j, r, cp)
            assert dt == want, (LT['name'], dt)
            LT['delta'], LT['target'] = dt, target
            sol[LT['name']] = sl
        m.probe.append((LC['name'], j, D, dict(eC=eC, sigma=sg, x=x, dN0=dN0, dZ0=dZ0, EN=LN['e'], eKZ=LZ['e'])))
    # 2. merge links
    for r in range(R):
        if incs[r]:
            sol['merge%d' % r] = solve_window(byname['merge%d' % r])
    # 3. inc: link (window at the merge unit), continue (window; far hairpin G_far)
    for i, ins in enumerate(prog):
        if ins[0] != 'inc':
            continue
        r = ins[1]
        Ll, Lc, Lm = byname['inc%d.link' % i], byname['inc%d.cont' % i], byname['merge%d' % r]
        sol[Ll['name']] = solve_window(Ll)
        g = sol[Ll['name']][1]
        a = N + r
        t = Ll['t']
        gm = mwl(UN[a]['io'][t]['D'], 0, 0, 30 * (slot(Ll, g) - slot(Ll, mwl(UN[a]['side'][t], 0, 0, 604))))
        pcs, g2, cor, legs = build(Lm, Lm['e'], g0=gm)
        assert window_res(Lm, g2) == Lm['rho']
        Ll['merge_legs'] = legs
        Ll['merge_g0'] = gm
        Ll['t_inc'] = time_at(g2, cross(Lm['gate']))
        Lc['G'] = 0
        sol[Lc['name']] = solve_window(Lc)
        # the continue at its up-turn corner (d_c, BACK_c) vs the INC control at the INC gate
        cu, cv = Lc['cdst'], Lc['BACK']
        t0 = tuv(sol[Lc['name']][3][3], cu, cv)
        Lc['G'] = 30 * -(-int(max(0, Ll['t_inc'] + 500 - t0)) // 120)
        Lc['slack0'] = t0 - (Ll['t_inc'] + 500)
        sol[Lc['name']] = solve_window(Lc)
        Lc['t_corner'] = tuv(sol[Lc['name']][3][3], cu, cv)
        Lc['slack'] = Lc['t_corner'] - (Ll['t_inc'] + 500)
        assert Lc['slack'] == Lc['slack0'] + 4 * Lc['G']
        m.probe.append((Lc['name'], 'slack', Lc['slack']))
        if not probe:
            assert Lc['slack'] >= 0, (Lc['name'], Lc['slack'])
    # 4. answers, timed from the caller's C'
    for i, ins in enumerate(prog):
        if ins[0] != 'dec':
            continue
        r = ins[1]
        j = decs[r].index(i)
        cp = byname['dec%d.C' % i]['Cp']
        shift = cp[2] - W(M['CP'], r)[2]
        for nm in ('nz', 'z'):
            La = byname['dec%d.%s' % (i, nm)]
            La['g0'] = mwl(W(M[nm][j][1], r), 0, 0, shift)
            sol[La['name']] = solve_window(La)
        Lz = byname['dec%d.z' % i]
        Lz['done'] = 30 * ((int(time_at(cp, (-1100 + U[r] // 2, -1100 - U[r] // 2))) - 400) // 30) + 27540
        Lz['slack'] = time_at(sol[Lz['name']][1], cross(Lz['gate'])) - (Lz['done'] + 300)
        m.probe.append((Lz['name'], 'slack', Lz['slack']))
        if not probe:
            assert Lz['slack'] >= 0, (Lz['name'], Lz['slack'])
    # 5. halt
    Lh = byname['halt%d' % ih]
    sol[Lh['name']] = build(Lh, 0)
    Lh['e'] = 0
    m.halt = sol[Lh['name']][1]
    for L in links:
        pcs, g, cor, legs = sol[L['name']]
        L['pieces'], L['final'], L['corners'], L['legs'] = pcs, g, cor, legs
        L['H'] = hair(L, L['e']) if L['dst'][0] != 'halt' else None
        for idx, p in enumerate(pcs):
            add(p, ('R', L['name'], idx))
    # start glider: side line of the start copy of unit 0, residue 5 of its window
    t0c = copy_for(0, ('start',), UN[0]['in_cols'][0] % 2)
    w = mwl(UN[0]['side'][t0c], 0, 0, 4)
    m.start = w
    m.start_t = 30 * (int(tuv(w, UN[0]['in_cols'][t0c] + 1, coord_of(w))) // 30)
    m.pieces, m.names, m.eaters = pieces, names, eaters
    umin = min(min(x - y for x, y in env_cells(p)) for p in pieces)
    hv = coord_of(m.halt)
    hu = umin - 600
    if (hu + hv) % 2:
        hu -= 1
    m.halt_cell_uv = (hu, hv)
    m.umin = umin
    return m


def delay_formulas(N, R, D, P, P_U, P_M, U_0, H_I):
    """The four delay rules (R-31 section 4); placeholders until fitted."""
    return {'G_far': None}


def blocks_of(m, values):
    c = set()
    for r in range(m.R):
        c |= translate(block(values.get(r, 0)), m.U[r] // 2, -m.U[r] // 2)
    return c


def describe(m, log=print):
    c = m.const
    log('N %d R %d D %d P %d; constants %s' % (m.N, m.R, m.D, m.P, c))
    log('units A_a %s at v %d; modules U_r %s' % (m.A, c['V_U'], m.U))
    for L in m.links:
        log('  b %2d s %d %-10s src col %6s dst col %6s OUT %6d BACK %6s H %7s e %2s %s -> %s' % (
            L['b'], L['s'], L['name'], L['csrc'], L['cdst'], L['OUT'], L['BACK'] if L['dst'][0] != 'halt' else '-', L['H'],
            L['e'], ('delta %d' % L['delta']) if 'delta' in L else ('rho %d' % L['rho'] if 'rho' in L else ''), wl(L['final'])))
    log('pieces %d, eater cells %d, start %s at t = %d, halt line %s, HALT cell uv %s' % (
        len(m.pieces), len(m.eaters), wl(m.start), m.start_t, wl(m.halt), m.halt_cell_uv))


PROGS = {
    'add': [('dec', 0, 3), ('inc', 1), ('dec', 2, 0), ('halt',)],
    'share': [('inc', 0), ('dec', 0, 3), ('dec', 0, 3), ('halt',)],
    # random program (seed 7 of p4_random.py): 3 registers, 7 instructions, every kind, r0 used 3x
    'rand': None,
}


def get_prog(name):
    if name in PROGS and PROGS[name] is not None:
        return PROGS[name]
    return json.load(open(os.path.join(LPRES, 'prog_%s.json' % name)))['prog']


if __name__ == '__main__':
    name = sys.argv[1] if len(sys.argv) > 1 else 'add'
    prog = [tuple(x) for x in get_prog(name)]
    m = layout(prog)
    describe(m)
