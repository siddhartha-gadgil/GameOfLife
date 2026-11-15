#!/usr/bin/env python3
"""L2 (R-30): the layout rule.  layout(program, regs_used) -> machine (pieces, eaters, blocks, start
glider, halt line, timing data).  Coordinates (u, v) = (x - y, x + y); see lcommon.py.

Program: list of ('inc', r) | ('dec', r, z) | ('halt',)   (CounterMachine.lean: inc r, decJz r z, halt;
'dec' on a nonzero register decrements and goes to i + 1, on zero jumps to z).

GLOBAL PLAN (all numbers in (u, v)):
  * register r: module M(nd_r) (l0_module) translated by xy (U_r / 2, -U_r / 2) (u-shift U_r, v-shift 0);
    its block diagonal is the ray u = U_r - 96, v >= 404.  Modules are side by side along u; every
    module has a LEFT channel zone (DEC, INC, NZ-token feeders going down, NZ answers going up) and a
    RIGHT channel zone (Z-token feeders going down, Z answers going up); zones of neighbouring
    modules do not interleave.  Inside a zone the channel nearer to the module is the shallower one,
    so no leg into / out of the module crosses another channel of the zone.
  * band: above every module (v < V_B); link k uses an OUT track h_k (moving SW, i.e. -u) and a BACK
    track h_k + S (moving NE, +u); a link is: source column -> out track -> hairpin at u = H_k
    (left of both columns, in a column-free place) -> back track -> destination column.  The
    hairpin position H_k is the timing knob: H_k -> H_k - 2 adds 8 generations.
  * instruction units (l1_parts.Unit) in a row above the band, merge units M_r (INC callers of r) too.
  * halt: the halt unit's output goes down to its own track and then SW forever (the HALT line).
"""
import sys
import json
from lcommon import *
from net import Net
import l0_module
import l1_parts

S_HAIR = 100          # out track -> back track
PITCH = 170           # between consecutive links' out tracks
COL = 60              # column spacing in a channel zone
W_DEC = list(range(1, 14))       # side window residues of the OR gate (relative to tau_lo - 1)
TOK_W = [-3, -1, 0, 1, 2, 7, 8, 9]
JOG_W = 60


def lane_of(d, c):
    return {SE: c, NW: -c, NE: -c, SW: c}[d]


def coord_of(w):
    d, lane, _ = w
    return {SE: lane, NW: -lane, NE: -lane, SW: lane}[d]


def is_u(d):
    return d in (SE, NW)


def fix(c, p):
    return c if c % 2 == p % 2 else c - 1


def route(g, turns):
    """Turns [(dir, coord)] applied to the glider g (coords parity-fixed here).  Returns
    (reflector pieces, final glider, corners [(u, v)], gliders per leg)."""
    pieces, corners, legs = [], [], [g]
    for (d, c) in turns:
        c = fix(c, 1 - coord_of(g) % 2)
        r = reflect(g, d, lane_of(d, c))
        assert r is not None, (g, d, c)
        rf, g = r
        pieces.append(rf)
        a, b = coord_of(legs[-1]), c
        corners.append((a, b) if is_u(legs[-1][0]) else (b, a))
        legs.append(g)
    return pieces, g, corners, legs


def arrive(w, pt_xy):
    return time_at(w, pt_xy)


class Machine:
    pass


def analyse(prog):
    regs = sorted({ins[1] for ins in prog if ins[0] != 'halt'})
    preds = {i: [] for i in range(len(prog))}
    preds[0].append(('start',))
    for i, ins in enumerate(prog):
        if ins[0] == 'inc':
            preds[i + 1].append(('cont', i))
        elif ins[0] == 'dec':
            preds[i + 1].append(('nz', i))
            preds[ins[2]].append(('z', i))
    decs = {r: [i for i, ins in enumerate(prog) if ins[0] == 'dec' and ins[1] == r] for r in regs}
    incs = {r: [i for i, ins in enumerate(prog) if ins[0] == 'inc' and ins[1] == r] for r in regs}
    return regs, preds, decs, incs


def module_data(nd):
    M = l0_module.module(nd)
    allc = set().union(*[env_cells(p) for p in M['pieces']]) | M['eaters']
    M['uvbox'] = l0_module.uvbox(allc)
    # DEC chain: input at copy t (tau_lo + 5 + 600) -> C' (exact)
    M['cprime'] = []
    for t, g in enumerate(M['dec_gates']):
        w = mwl(M['dec'][t], 0, 0, 5 + 600)
        st, outs, _, _ = Net(M['dec_gates']).react([w], limit=4000, t_hint=7000)
        assert st == 'ok' and len(outs) == 1 and outs[0][:2] == (SE, 41)
        M['cprime'].append((w, outs[0]))
    return M


_MOD = {}


def mod(nd):
    if nd not in _MOD:
        _MOD[nd] = module_data(nd)
    return _MOD[nd]


def window_slot(w, wlo):
    """For a glider w on the line of the window family wlo = (d, lane, tau_lo) (residue 1 = tau_lo):
    the slot m with w.tau in tau_lo + 30 m .. tau_lo + 12 + 30 m, or None."""
    assert w[:2] == wlo[:2], (w, wlo)
    dt = w[2] - wlo[2]
    m, r = divmod(dt, 30)
    return m if 0 <= r <= 12 else None




def mw(M_U, w):
    """Module-local world line -> world (module r at u-shift M_U)."""
    return mwl(w, M_U // 2, -M_U // 2)


def layout(prog, verbose=False):
    regs, preds, decs, incs = analyse(prog)
    m = Machine()
    m.prog, m.regs, m.decs, m.incs, m.preds = prog, regs, decs, incs, preds
    pieces, names, eaters = [], [], set()

    def add(p, name):
        pieces.append(p)
        names.append(name)

    # ---------------- modules: side by side along u, v-shift 0 ----------------------------------
    U, mods, chan, port = {}, {}, {}, {}
    u_cur = None
    for r in regs:
        nd = len(decs[r])
        M = mod(nd)
        mods[r] = M
        ub = M['uvbox']
        nleft, nright = 2 * nd + 1 + 2 * nd, 2 * nd
        left_w = -ub[0] + 100 + COL * nleft + 60
        Ur = left_w if u_cur is None else u_cur + left_w
        Ur += Ur % 2
        U[r] = Ur
        u_cur = Ur + ub[2] + 100 + COL * nright + 60
        for p in M['pieces']:
            add(move(p, Ur // 2, -Ur // 2), 'M%d' % r)
        eaters |= set(translate(M['eaters'], Ur // 2, -Ur // 2))
        W = lambda w: mw(Ur, w)
        # port data (world): ('in' ports) final line + window base; channel columns with parity
        L0 = Ur + ub[0] - 100
        idx = 0
        for t in range(2 * nd):
            w = W(M['dec'][t])
            port[(r, 'dec%d' % t)] = {'line': w, 'gate': move(M['dec_gates'][t], Ur // 2, -Ur // 2),
                                       'suffix': [(NE, coord_of(w))], 'cprime': (W(M['cprime'][t][0]), W(M['cprime'][t][1]))}
            chan[(r, 'dec%d' % t)] = fix(L0 - COL * idx, 1 - coord_of(w) % 2)
            idx += 1
        w = W(M['inc'][0])
        port[(r, 'inc')] = {'line': w, 'gate': move(M['inc_gates'][0], Ur // 2, -Ur // 2), 'suffix': [(NE, coord_of(w))]}
        chan[(r, 'inc')] = fix(L0 - COL * idx, 1 - coord_of(w) % 2)
        idx += 1
        CPw = W(M['CP'])
        for j in range(nd):
            K, Sp = W(M['nz'][j][0]), W(M['nz'][j][1])
            port[(r, 'nztok%d' % j)] = {'line': K, 'suffix': [(NE, coord_of(K))], 'ref': CPw}
            chan[(r, 'nztok%d' % j)] = fix(L0 - COL * idx, 1 - coord_of(K) % 2)
            idx += 1
            port[(r, 'nzret%d' % j)] = {'src': Sp, 'ref': CPw}
            chan[(r, 'nzret%d' % j)] = fix(L0 - COL * idx, 1 - coord_of(Sp) % 2)
            idx += 1
        R0 = Ur + ub[2] + 100
        idx = 0
        for j in reversed(range(nd)):
            vd = 900 + 160 * (nd - 1 - j)
            K, Sp = W(M['z'][j][0]), W(M['z'][j][1])
            port[(r, 'zret%d' % j)] = {'src': Sp, 'ref': CPw, 'prefix_v': fix(vd, 1 - coord_of(Sp) % 2)}
            chan[(r, 'zret%d' % j)] = fix(R0 + COL * idx, coord_of(Sp) % 2)
            idx += 1
            port[(r, 'ztok%d' % j)] = {'line': K, 'suffix': [(SW, vd + 80), (NW, coord_of(K))], 'ref': CPw}
            chan[(r, 'ztok%d' % j)] = fix(R0 + COL * idx, coord_of(K) % 2)
            idx += 1
        # DZ2 completion time for C' = CP (world): Ts + 27540 (f8_full.py)
        M['done_off'] = None
        fb = (-1100 + Ur // 2, -1100 - Ur // 2)
        port[(r, 'done')] = lambda cp, fb=fb: 30 * ((int(time_at(cp, fb)) - 400) // 30) + 27540
    V_B = min(mods[r]['uvbox'][1] for r in regs) - 200
    m.U, m.mods, m.chan, m.port = U, mods, chan, port
    # ---------------- units: a row left of all modules, above the band -------------------------
    ukeys = []
    for i, ins in enumerate(prog):
        ukeys.append((('I', i), ins[0] if ins[0] != 'halt' else 'halt', preds[i]))
    for r in regs:
        if incs[r]:
            ukeys.append((('M', r), 'merge', [('link', i) for i in incs[r]]))
    UN = {}
    widths = []
    for key, kind, pr in ukeys:
        T_ = l1_parts.unit(kind, 2 * max(1, len(pr)))
        UN[key] = {'T': T_, 'kind': kind, 'preds': pr}
        widths.append(T_.width[1] - T_.width[0] + 160)
    a = min(chan.values()) - 300 - sum(widths)
    for key, kind, pr in ukeys:
        d = UN[key]
        d['A'] = a - d['T'].width[0]
        a += d['T'].width[1] - d['T'].width[0] + 160
    # merge units: output column parity = INC port channel parity
    for r in regs:
        if incs[r]:
            d = UN[('M', r)]
            if (d['T'].cols['D'][1] + d['A']) % 2 != chan[(r, 'inc')] % 2:
                d['A'] -= 1
    # ---------------- links ----------------------------------------------------------------------
    links = []
    for i, ins in enumerate(prog):
        key = ('I', i)
        if ins[0] == 'inc':
            links.append({'name': 'inc%d.link' % i, 'src': ('unit', key, 'D'), 'dst': ('unit', ('M', ins[1]), ('link', i)), 'act': i})
            links.append({'name': 'inc%d.cont' % i, 'src': ('unit', key, 'R'), 'dst': ('unit', ('I', i + 1), ('cont', i)), 'act': i})
        elif ins[0] == 'dec':
            r = ins[1]
            j = decs[r].index(i)
            for o in ('C', 'KNZ', 'KZ'):
                links.append({'name': 'dec%d.%s' % (i, o), 'src': ('unit', key, o), 'dst': ('port', r, o, j), 'act': i})
            links.append({'name': 'dec%d.nz' % i, 'src': ('ret', r, 'nzret%d' % j, i), 'dst': ('unit', ('I', i + 1), ('nz', i)), 'act': ('nz', i)})
            links.append({'name': 'dec%d.z' % i, 'src': ('ret', r, 'zret%d' % j, i), 'dst': ('unit', ('I', ins[2]), ('z', i)), 'act': ('z', i)})
        else:
            links.append({'name': 'halt%d' % i, 'src': ('unit', key, 'D'), 'dst': ('halt',), 'act': i})
    for r in regs:
        if incs[r]:
            links.append({'name': 'merge%d' % r, 'src': ('unit', ('M', r), 'D'), 'dst': ('port', r, 'INC', 0), 'act': ('M', r)})
    nl = len(links)
    V_T = V_B - PITCH * nl
    Vu = V_T - 200 - max(d['T'].uvbox[3] for d in UN.values())
    for key, d in UN.items():
        V = Vu if (d['A'] - Vu) % 2 == 0 else Vu - 1
        d['V'] = V
        d['dxy'] = ((d['A'] + V) // 2, (V - d['A']) // 2)
        for p in d['T'].pieces:
            add(move(p, *d['dxy']), 'U%s%s' % key)
        d['out'] = {k: mwl(w, *d['dxy']) for k, w in d['T'].io[0].items()}
        d['io'] = [{k: mwl(w, *d['dxy']) for k, w in io.items()} for io in d['T'].io]
        d['side'] = [mwl(w, *d['dxy']) for w in d['T'].side]
        d['gates'] = [move(g, *d['dxy']) for g in d['T'].gates]
        d['in_cols'] = [c + d['A'] for c in d['T'].in_cols]
        d['free'] = list(range(d['T'].n))
        d['copy'] = {}
    # decJz output assignment by parity (tokens to the columns of matching parity)
    for i, ins in enumerate(prog):
        if ins[0] == 'dec':
            r = ins[1]
            j = decs[r].index(i)
            d = UN[('I', i)]
            pD = coord_of(d['out']['D']) % 2
            if pD == chan[(r, 'nztok%d' % j)] % 2:
                d['assign'] = {'KNZ': 'D', 'KZ': 'R', 'C': 'L'}
            else:
                d['assign'] = {'KZ': 'D', 'KNZ': 'R', 'C': 'L'}
            assert coord_of(d['out'][d['assign']['KZ']]) % 2 == chan[(r, 'ztok%d' % j)] % 2
    for k, L in enumerate(links):
        L['h'] = V_T + PITCH * k
        L['hb'] = L['h'] + S_HAIR
    m.V_B, m.V_T, m.Vu, m.UN, m.links = V_B, V_T, Vu, UN, links

    # source glider, source column, prefix turns; destination column, final turns
    def take_copy(key, pr, parity):
        d = UN[key]
        if pr in d['copy']:
            return d['copy'][pr]
        for t in d['free']:
            if parity is None or d['in_cols'][t] % 2 == parity % 2:
                d['free'].remove(t)
                d['copy'][pr] = t
                return t
        raise RuntimeError('no copy of parity %s left at %s' % (parity, key))

    for L in links:
        s = L['src']
        if s[0] == 'unit':
            d = UN[s[1]]
            o = d['assign'][s[2]] if 'assign' in d else s[2]
            L['g0'] = d['out'][o]          # representative (input at copy 0, slot 20)
            L['prefix'] = []
            L['csrc'] = coord_of(L['g0'])
            L['src_from'] = 'above'
        else:
            _, r, nm, i = s
            P = port[(r, nm)]
            L['prefix'] = [(NW, chan[(r, nm)])] if nm.startswith('nz') else [(NE, P['prefix_v']), (NW, chan[(r, nm)])]
            L['csrc'] = chan[(r, nm)]
            L['src_from'] = 'below'
        dd = L['dst']
        if dd[0] == 'unit':
            t = take_copy(dd[1], dd[2], L['csrc'] % 2)
            d = UN[dd[1]]
            L['cdst'] = d['in_cols'][t]
            L['suffix'] = [(NW, L['cdst']), (NE, coord_of(d['side'][t]))]
            L['wlo'] = d['side'][t]
            L['gate'] = d['gates'][t]
        elif dd[0] == 'port':
            _, r, o, j = dd
            if o == 'C':
                cand = [t for t in (2 * j, 2 * j + 1) if chan[(r, 'dec%d' % t)] % 2 == L['csrc'] % 2]
                t = cand[0]
                nm = 'dec%d' % t
            elif o == 'INC':
                nm = 'inc'
            elif o == 'KNZ':
                nm = 'nztok%d' % j
            else:
                nm = 'ztok%d' % j
            assert chan[(r, nm)] % 2 == L['csrc'] % 2, (L['name'], nm)
            L['port'] = (r, nm)
            L['cdst'] = chan[(r, nm)]
            L['suffix'] = [(SE, L['cdst'])] + port[(r, nm)]['suffix']
            L['wlo'] = port[(r, nm)]['line']
            L['gate'] = port[(r, nm)].get('gate')
        else:
            L['cdst'] = None
            L['suffix'] = []
    # start input of instruction 0
    t0c = take_copy(('I', 0), ('start',), None)
    m.start_copy = t0c
    # ---------------- column segments (for the hairpin free test) -----------------------------
    cols = []
    for L in links:
        top_unit = Vu
        if L['src_from'] == 'above':
            cols.append((L['csrc'], top_unit, L['h']))
        else:
            cols.append((L['csrc'], L['h'], V_B + 400))
        if L['cdst'] is not None:
            if L['dst'][0] == 'unit':
                cols.append((L['cdst'], top_unit, L['hb']))
            else:
                cols.append((L['cdst'], L['hb'], V_B + 400))
    m.cols = cols

    def free(H, L):
        if H > min(L['csrc'], L['cdst']) - 70:
            return False
        for (c, v0, v1) in cols:
            if abs(c - H) < 70 and v0 - 50 <= L['hb'] and v1 + 50 >= L['h']:
                return False
        return True

    def build(L, H, g0=None, jog=0):
        """jog = 1: the hairpin makes one step (SE -> SW at h + 50, SW -> SE at H - JOG_W): two more
        turns, 2 JOG_W more length: arrival + 4 JOG_W - 10 = +230 (= 6 mod 8)."""
        g0 = L['g0'] if g0 is None else g0
        band = [(SW, L['h']), (SE, H)] + ([(SW, L['h'] + 50), (SE, H - JOG_W)] if jog else []) + [(NE, L['hb'])]
        turns = L['prefix'] + band + L['suffix']
        return route(g0, turns)

    def candidates(L, jog=0):
        H = fix(min(L['csrc'], L['cdst']) - 70, L['csrc'] % 2)
        while True:
            if free(H, L) and (not jog or free(H - JOG_W, L)):
                yield H
            H -= 2

    def solve_window(L, extra=None):
        """First H (from the right) whose final glider is inside the destination window (and
        extra(final) holds)."""
        for H in candidates(L):
            pcs, g, cor, legs = build(L, H)
            if window_slot(g, L['wlo']) is not None and (extra is None or extra(g)):
                return H, pcs, g, cor, legs
            if H < -60000:
                raise RuntimeError('no H for %s' % L['name'])

    def gate_time(L, g):
        return time_at(g, cross(L['gate']))

    sol = {}
    byname = {L['name']: L for L in links}
    # 1. DECJZ calls: C, then the tokens exactly
    for i, ins in enumerate(prog):
        if ins[0] != 'dec':
            continue
        r = ins[1]
        j = decs[r].index(i)
        LC, LN, LZ = byname['dec%d.C' % i], byname['dec%d.KNZ' % i], byname['dec%d.KZ' % i]
        found = None
        # pass 1: plain hairpins, the first 12 admissible slots of C; pass 2: one jog allowed in
        # a token route (always solvable within 4 slots, see R-30 §4)
        for allow_jog in (False, True):
            slots = 0
            for HC in candidates(LC):
                pcs, g, cor, legs = build(LC, HC)
                mC = window_slot(g, LC['wlo'])
                if mC is None:
                    continue
                slots += 1
                w_in, cp = port[LC['port']]['cprime']
                cp = mwl(cp, 0, 0, 30 * (mC - 20))
                shift = cp[2] - port[LN['port']]['ref'][2]
                ok = []
                for LT in (LN, LZ):
                    target = mwl(port[LT['port']]['line'], 0, 0, shift)
                    hit = None
                    for jog in ((0, 1) if allow_jog else (0,)):
                        for H in candidates(LT, jog):
                            p2, g2, c2, l2 = build(LT, H, jog=jog)
                            assert g2[:2] == target[:2], (g2, target)
                            dt = g2[2] - target[2]
                            if dt in TOK_W:
                                hit = (H, p2, g2, c2, l2)
                                LT['jog'] = jog
                                break
                            if dt > 9:
                                break
                        if hit:
                            break
                    ok.append(hit)
                if all(ok):
                    found = ((HC, pcs, g, cor, legs), ok, cp)
                    break
                if not allow_jog and slots >= 12:
                    break
                if HC < min(LC['csrc'], LC['cdst']) - 40000:
                    raise RuntimeError('no token timing for dec %d' % i)
            if found:
                break
        (c_sol, (n_sol, z_sol), cp) = found
        sol[LC['name']], sol[LN['name']], sol[LZ['name']] = c_sol, n_sol, z_sol
        UN[('I', i)]['cprime'] = cp
    # 2. merge links (window at the INC port)
    for r in regs:
        if incs[r]:
            sol['merge%d' % r] = solve_window(byname['merge%d' % r])
    # 3. inc links, then continues (>= INC port arrival + 500)
    for i, ins in enumerate(prog):
        if ins[0] != 'inc':
            continue
        r = ins[1]
        Ll = byname['inc%d.link' % i]
        sol[Ll['name']] = solve_window(Ll)
        g = sol[Ll['name']][2]
        dM = UN[('M', r)]
        t = dM['copy'][('link', i)]
        mslot = window_slot(g, dM['side'][t])
        gm = mwl(dM['io'][t]['D'], 0, 0, 30 * (mslot - 20))
        Lm = byname['merge%d' % r]
        pcs, g2, cor, legs = build(Lm, sol[Lm['name']][0], g0=gm)
        assert window_slot(g2, Lm['wlo']) is not None
        Ll['merge_legs'] = legs            # the merge link as actually run after this INC link
        t_inc = gate_time(Lm, g2)
        Lc = byname['inc%d.cont' % i]
        sol[Lc['name']] = solve_window(Lc, extra=lambda gg, Lc=Lc, t_inc=t_inc: gate_time(Lc, gg) >= t_inc + 500)
        Lc['t_inc'] = t_inc
    # 4. answers (sources timed by the caller's C')
    for i, ins in enumerate(prog):
        if ins[0] != 'dec':
            continue
        r = ins[1]
        j = decs[r].index(i)
        cp = UN[('I', i)]['cprime']
        shift = cp[2] - port[(r, 'nzret%d' % j)]['ref'][2]
        Ln, Lz = byname['dec%d.nz' % i], byname['dec%d.z' % i]
        Ln['g0'] = mwl(port[(r, 'nzret%d' % j)]['src'], 0, 0, shift)
        Lz['g0'] = mwl(port[(r, 'zret%d' % j)]['src'], 0, 0, shift)
        done = port[(r, 'done')](cp)
        Lz['done'] = done
        sol[Ln['name']] = solve_window(Ln)
        sol[Lz['name']] = solve_window(Lz, extra=lambda gg, Lz=Lz, done=done: gate_time(Lz, gg) >= done + 300)
    # 5. halt: down to its track, then SW forever
    for L in links:
        if L['dst'][0] == 'halt':
            pcs, g, cor, legs = route(L['g0'], [(SW, L['h'])])
            sol[L['name']] = (None, pcs, g, cor, legs)
            m.halt = g
    for L in links:
        H, pcs, g, cor, legs = sol[L['name']]
        L['H'], L['pieces'], L['final'], L['corners'], L['legs'] = H, pcs, g, cor, legs
        for p in pcs:
            add(p, 'R:' + L['name'])
    # start glider: on the side line of instruction 0's start copy, at its input column
    d0 = UN[('I', 0)]
    t = m.start_copy
    w = mwl(d0['side'][t], 0, 0, 5)
    v = coord_of(w)
    P = xy(d0['in_cols'][t] + (1 if (d0['in_cols'][t] + v) % 2 else 0), v)
    m.start = w
    m.start_t = 30 * (int(time_at(w, P)) // 30)
    m.pieces, m.names, m.eaters = pieces, names, eaters
    m.halt_line = m.halt
    return m


def blocks_of(m, values):
    """Register blocks for the register values {r: k}."""
    c = set()
    for r in m.regs:
        c |= translate(block(values.get(r, 0)), m.U[r] // 2, -m.U[r] // 2)
    return c


def describe(m):
    print('registers %s: module u-shifts %s; band v %d .. %d; units at v %d' % (m.regs, m.U, m.V_T, m.V_B, m.Vu))
    for key, d in m.UN.items():
        print('  unit %s %s n=%d at uv (%d, %d), copies %s %s' % (key, d['kind'], d['T'].n, d['A'], d['V'], d['copy'], d.get('assign', '')))
    for L in m.links:
        print('  link %-12s h %d H %s src col %s dst col %s -> %s' % (L['name'], L['h'], L['H'], L['csrc'], L['cdst'], wl(L['final'])))
    print('  pieces %d, eater cells %d, start %s at t = %d, halt line %s' % (len(m.pieces), len(m.eaters), wl(m.start), m.start_t, wl(m.halt)))


if __name__ == '__main__':
    prog = [('dec', 0, 3), ('inc', 1), ('dec', 2, 0), ('halt',)]
    m = layout(prog)
    describe(m)
