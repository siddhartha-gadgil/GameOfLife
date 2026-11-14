#!/usr/bin/env python3
"""Cell-exact data of the register of report R-24 (one block, a pull input DEC and a push input INC),
every statement re-checked with the set simulator on the unbounded plane.

Usage: report24.py --pick DESIGN_INDEX FILE.json.gz I results/register.json
       report24.py results/register.json [--seq]           (--seq: only the INC/DEC sequence tests)
"""
import gzip
import json
import os
import sys

from common import (glider_at, evolve_cells, counter, translate, bbox, SE, SW, NW, NE, life, DIRNAME)
from reactions import shift_wl
import net
from net import Net, piece_cells, env_cells, time_at, asm_cross, rf_point, wlname, pr, reflect_to
from g2_pull import reflect
from report22 import describe, clearances
import j2_pocket as J
import j3_stage as J3
import j4_inc as J4
import j6_inc as J6

NAMES = J6.NAMES


def tup(o):
    return (tuple(o[0]), o[1], o[2])


def load(path):
    d = json.load(open(path))
    d['pieces'] = [tuple(p) for p in d['pieces']]
    for k in ('w', 's1', 'cin', 'e', 'c', 'a', 'b', 'bp', 'C_I'):
        d[k] = tup(d[k])
    return d


def rebuild(d, rec):
    """All world lines and pieces of the design, by name."""
    sol = rec['sol']
    P = dict(zip(NAMES, d['pieces']))
    W = {}
    rf1, rf2, rf3 = [tuple(r) for r in sol['rfs']]
    W['C0'] = J4.C0
    W['G1'] = (NW, 29, 730)
    W['leg'] = reflect(W['G1'], SW, J.g4._lane_of_leg(rf1))[1]
    W['a'] = d['a']
    W['G2'] = (SW, 75, 771)
    o = sol['gb_out']
    W['o'] = (tuple(o[0]), o[1], o[2])
    W['b'] = d['b']
    k, X, Y, s = d['frame']
    cx = J4.core_exact(J4.CORE[d['core']], d['w'], d['s1'], X, Y)
    assert cx['frame'] == tuple(d['frame'])
    W['g1c'], W['legc'], W['g2c'] = cx['g1'], cx['leg'], cx['g2']
    W['w'], W['s1'] = d['w'], d['s1']
    W['gin'] = reflect_to(d['e'], SW, 0)[1]
    # the input of RF_e: the SW world line turned into e by the piece RFe
    for j in range(-400, 400):
        q, gi = reflect_to(d['e'], SW, j)
        if q == P['RFe']:
            W['gin'] = gi
            break
    W['e'] = d['e']
    for (w, oo) in J.or_controls(sol, [P['RFe'], P['Rp']]):
        if w == d['w']:
            W['o2'] = oo
    W['bp'] = d['bp']
    ctrl = shift_wl(J4.C0, X, Y, s)
    j4, la, lb, lc = d['jog']
    J4p, sw = reflect_to(ctrl, SW, j4)
    J3p, nw = reflect_to(sw, NW, j4 + la)
    J2p, ne = reflect_to(nw, NE, j4 + la + lb)
    J1p, link = reflect_to(ne, SE, j4 + la + lb - lc)
    assert (J1p, J2p, J3p, J4p) == (P['J1'], P['J2'], P['J3'], P['J4'])
    W['ctrl'], W['sw'], W['nw'], W['ne'], W['link'] = ctrl, sw, nw, ne, link
    fu = J4.UPS[d['U']]
    g = fu['G1']
    vx = d['ux']
    vy = vx - (link[1] - g[1])
    su = link[2] - g[2] + 4 * vx
    W['cont'] = shift_wl(fu['G2'], vx, vy, su)
    W['C_I'] = d['C_I']
    for (Ra, ctl, Gc) in J6.gate_ne(W['cont'], d['cin']):
        if (Ra, Gc) == (P['Ra'], P['Gc']):
            W['ctl'] = ctl
    W['cin'] = d['cin']
    W['c'] = d['c']
    return P, W


def main():
    if sys.argv[1] == '--pick':
        di = int(sys.argv[2])
        d = json.load(gzip.open(sys.argv[3], 'rt'))[int(sys.argv[4])]
        d['design'] = di
        json.dump(d, open(sys.argv[5], 'w'))
        return
    seq_only = '--seq' in sys.argv
    args = [x for x in sys.argv[1:] if x != '--seq']
    d = load(args[0])
    recs = json.load(gzip.open(J3.POCKET_FILE, 'rt'))
    rec = recs[d['design']]
    P, W = rebuild(d, rec)
    pieces = d['pieces']
    C0, CI = W['C0'], W['C_I']
    note = (' pull salvo (DEC) = pullSalvo {a, b}; push salvo (INC) = {e, b\', c} = push %s\n' % (
                '(5, -47), (11, -25), (-5, 0)' if J3.PUSH == 5 else '(5, -51), (12, -24), (-6, 0)') +
            ' of results/p1_pushes.json (lanes and taus relative to the block); b and b\' leave the same reflector RF3,\n'
            ' released by the gate Gb from its two control gliders G2 (DEC) and w (INC): Gb is an OR gate')
    if seq_only:
        nt = Net(pieces, NAMES)
        L = W['a'][1]
        dy = nt.env[3] + 30 - 11
        dx = (L + 1) + 4 + dy
        sequences(nt, W, C0, CI, dx, dy)
        return
    nt, Ts1, Te1, outs1, start1, end1 = describe('REGISTER (j6_inc.py): pull generator (S, K, Gb, RF1, RF2, RF3) + push part '
                                                 '(RFe, Rp, RFc; core Sc, Kc, RF1c, RF2c, Rw; U = Su, Ku; loop J1..J4; Ra, Gc)\n'
                                                 'INPUT DEC (control C0):', pieces, NAMES, [C0], [W['a'], W['b']], [300, 330, 360], note=note)
    print('INPUT INC (control C_I):')
    st, outs2, Ts2, Te2 = nt.react([CI], limit=20000)
    assert st == 'ok' and outs2 == sorted([W['e'], W['bp'], W['c']]), (st, outs2)
    end2, box2 = nt.trace([CI], Ts2, Te2)
    exp2 = nt.cycle(Te2)
    for w in outs2:
        exp2 |= glider_at(*w, Te2)
    assert end2 == exp2
    print(' reaction (set simulator, unbounded plane):  evolve %d (R ∪ C_I) = R ∪ G   (world times %d -> %d)' % (Te2 - Ts2, Ts2, Te2))
    pr('C_I %s' % wlname(CI), glider_at(*CI, Ts2))
    for i, w in enumerate(outs2):
        pr('G%d %s' % (i + 1, wlname(w)), glider_at(*w, Te2))
    pr('end R ∪ G', end2)
    print('  box of all generations of the reaction: x %d..%d, y %d..%d' % (box2[0], box2[2], box2[1], box2[3]))
    for T in range(300, 1500, 30):
        c2 = [CI, (CI[0], CI[1], CI[2] + T)]
        st3, o3, a3, b3 = nt.react(c2, limit=20000)
        good = st3 == 'ok' and o3 == sorted(outs2 + [(w[0], w[1], w[2] + T) for w in outs2])
        print(' second INC control glider %d generations later: %s' % (T, 'works (set simulator)' if good else 'FAILS'))
        if good:
            break
    # flight segments
    Tm = lambda w, p: int(time_at(w, p))
    X = lambda n: asm_cross(P[n])
    R = lambda n: rf_point(P[n])
    segs = [('DEC control C0', C0, Ts1, Tm(C0, X('S')) - 20, ['S']),
            ('G1 (K to RF1)', W['G1'], Tm(W['G1'], X('K')) + 60, Tm(W['G1'], R('RF1')) - 20, ['K', 'RF1']),
            ('leg (RF1 to RF2)', W['leg'], Tm(W['leg'], R('RF1')) + 20, Tm(W['leg'], R('RF2')) - 20, ['RF1', 'RF2']),
            ('a (RF2 on)', W['a'], Tm(W['a'], R('RF2')) + 20, Te1 + 300, ['RF2']),
            ('G2 (S to Gb)', W['G2'], Tm(W['G2'], X('S')) + 20, Tm(W['G2'], X('Gb')) - 10, ['S', 'Gb']),
            ('o (Gb to RF3)', W['o'], Tm(W['o'], X('Gb')) + 40, Tm(W['o'], R('RF3')) - 20, ['Gb', 'RF3']),
            ('b (RF3 on)', W['b'], Tm(W['b'], R('RF3')) + 20, Te1 + 300, ['RF3']),
            ('INC control C_I', CI, Ts2, Tm(CI, X('Su')) - 20, ['Su']),
            ('link (Ku to J1)', W['link'], Tm(W['link'], X('Ku')) + 60, Tm(W['link'], R('J1')) - 20, ['Su', 'Ku', 'J1']),
            ('loop NE (J1 to J2)', W['ne'], Tm(W['ne'], R('J1')) + 20, Tm(W['ne'], R('J2')) - 20, ['J1', 'J2']),
            ('loop NW (J2 to J3)', W['nw'], Tm(W['nw'], R('J2')) + 20, Tm(W['nw'], R('J3')) - 20, ['J2', 'J3']),
            ('loop SW (J3 to J4)', W['sw'], Tm(W['sw'], R('J3')) + 20, Tm(W['sw'], R('J4')) - 20, ['J3', 'J4']),
            ('ctrl (J4 to Sc)', W['ctrl'], Tm(W['ctrl'], R('J4')) + 20, Tm(W['ctrl'], X('Sc')) - 20, ['J4', 'Sc', 'Kc']),
            ('g1c (Kc to RF1c)', W['g1c'], Tm(W['g1c'], X('Kc')) + 60, Tm(W['g1c'], R('RF1c')) - 20, ['Kc', 'RF1c']),
            ('legc (RF1c to RF2c)', W['legc'], Tm(W['legc'], R('RF1c')) + 20, Tm(W['legc'], R('RF2c')) - 20, ['RF1c', 'RF2c']),
            ('s1 (RF2c to Rp)', W['s1'], Tm(W['s1'], R('RF2c')) + 20, Tm(W['s1'], R('Rp')) - 20, ['RF2c', 'Rp']),
            ('gin (Rp to RFe)', W['gin'], Tm(W['gin'], R('Rp')) + 20, Tm(W['gin'], R('RFe')) - 20, ['Rp', 'RFe']),
            ('e (RFe on)', W['e'], Tm(W['e'], R('RFe')) + 20, Te2 + 300, ['RFe']),
            ('g2c (Sc to Rw)', W['g2c'], Tm(W['g2c'], X('Sc')) + 20, Tm(W['g2c'], R('Rw')) - 20, ['Sc', 'Rw']),
            ('w (Rw to Gb)', W['w'], Tm(W['w'], R('Rw')) + 20, Tm(W['w'], X('Gb')) - 120, ['Rw', 'Gb']),
            ("o' (Gb to RF3)", W['o2'], Tm(W['o2'], X('Gb')) + 40, Tm(W['o2'], R('RF3')) - 20, ['Gb', 'RF3']),
            ("b' (RF3 on)", W['bp'], Tm(W['bp'], R('RF3')) + 20, Te2 + 300, ['RF3']),
            ('cont (Su to Ra)', W['cont'], Tm(W['cont'], X('Su')) + 60, Tm(W['cont'], R('Ra')) - 20, ['Su', 'Ku', 'Ra']),
            ('ctl (Ra to Gc)', W['ctl'], Tm(W['ctl'], R('Ra')) + 20, Tm(W['ctl'], X('Gc')) - 120, ['Ra', 'Gc']),
            ('cin (Gc to RFc)', W['cin'], Tm(W['cin'], X('Gc')) + 40, Tm(W['cin'], R('RFc')) - 20, ['Gc', 'RFc']),
            ('c (RFc on)', W['c'], Tm(W['c'], R('RFc')) + 20, Te2 + 300, ['RFc'])]
    clearances(pieces, NAMES, segs)
    # the register block: counter k on lane L + 1, below the envelope
    L = W['a'][1]
    env = nt.env
    ymin = env[3] + 30
    dy = ymin - 11
    dx = (L + 1) + 4 + dy
    print(' register block B_k = translate (%d, %d) (counter k)  (upper left cell (%d + k, %d + k))' % (dx, dy, 7 + dx, 11 + dy))
    # salvos in the frame of counter 0
    for nm, ws, Te, dk in (('pull salvo (DEC)', [W['a'], W['b']], Te1, -1), ('push salvo (INC)', [W['e'], W['bp'], W['c']], Te2, 1)):
        wl0 = [(SE, w[1] - dx + dy, w[2] + 4 * dx) for w in ws]     # translated by (-dx, -dy)
        b0 = set(counter(0))
        lead = max(w[2] for w in wl0)
        for t0 in range(lead - 60, lead - 2000, -1):
            if (t0 - Te) % 4:
                continue                      # same phase as at the end of the reaction
            cells = [glider_at(*w, t0) for w in wl0]
            if all(life.chebyshev_dist(c, b0) >= 3 for c in cells) and all(
                    life.chebyshev_dist(cells[i], cells[j]) >= 3 for i in range(len(cells)) for j in range(i)):
                break
        sal = set().union(*cells)
        n = None
        for q in range(1, 600):
            if evolve_cells(sal | b0, q) == set(counter(dk)):
                n = q
                break
        assert n is not None
        for k in range(0, 6):
            assert evolve_cells(sal | set(counter(k)), n + 4 * k) == set(counter(k + dk))
        print(' %s in the frame of counter 0: world lines %s' % (nm, ', '.join(wlname(w) for w in wl0)))
        pr('  salvo at time %d' % t0, sal)
        print('    evolve %d (salvo ∪ counter 0) = counter %d; evolve (%d + 4 k) (salvo ∪ counter k) = counter (k %+d), k = 0..5: checked' % (n, dk, n, dk))
        G = set()
        for w in ws:
            G |= glider_at(*w, Te)
        sb, gb = bbox(sal), bbox(G)
        tx, ty = gb[0] - sb[0], gb[1] - sb[1]
        assert G == translate(sal, tx, ty)
        print('    at the end of the reaction the salvo is translate (%d, %d) of this window' % (tx, ty))
    # block tests
    for nm, ctr, Ts, Te, dk in (('DEC', [C0], Ts1, Te1, -1), ('INC', [CI], Ts2, Te2, 1)):
        for k in (0, 1, 2, 3, 4, 40):
            B = translate(set(counter(k)), dx, dy)
            n = 30 * ((Te - Ts + 4 * (k + 40) + 900) // 30)
            fin, box = nt.trace(ctr, Ts, Ts + n, extra=B)
            assert fin == nt.cycle(Ts + n) | translate(set(counter(k + dk)), dx, dy), (nm, k)
            print(' %s, k = %2d: evolve %d (R ∪ C ∪ B_%d) = R ∪ B_%d: checked; box x %d..%d, y %d..%d' % (
                nm, k, n, k, k + dk, box[0], box[2], box[1], box[3]))
    sequences(nt, W, C0, CI, dx, dy)


def sequences(nt, W, C0, CI, dx, dy):
    # both inputs in sequence: the second control is delayed by delta (a multiple of 30) against its
    # natural time; the salvo arrival gap is measured at the block (times at which the leading glider
    # of each salvo reaches the diagonal position of B_0)
    arr = {}
    for nm, ws in (('DEC', [W['a'], W['b']]), ('INC', [W['e'], W['bp'], W['c']])):
        arr[nm] = int(round(min(time_at(w, (7 + dx, 11 + dy)) for w in ws)))
    print(' salvo arrival times at B_0 (natural control times): DEC %d, INC %d' % (arr['DEC'], arr['INC']))

    def seq_ok(ctr, k):
        B = translate(set(counter(k)), dx, dy)
        st, o, a_, b_ = nt.react(ctr, limit=20000)
        if st != 'ok':
            return False, None, None
        n = 30 * ((b_ - a_ + 4 * (k + 40) + 1500) // 30)
        fin, box = nt.trace(ctr, a_, a_ + n, extra=B)
        return fin == nt.cycle(a_ + n) | B, n, box

    orders = (('INC', 'DEC'), ('DEC', 'INC'))
    if os.environ.get('R24_ORDER'):
        orders = [orders[int(os.environ['R24_ORDER'])]]
    for (fn, sn) in orders:
        first = CI if fn == 'INC' else C0
        second = C0 if sn == 'DEC' else CI
        base = arr[sn] - arr[fn]                 # gap with natural times
        # coarse scan downwards (steps of 120) from a gap of about 1200, then upwards in steps of 30
        d0 = 30 * ((1200 - base) // 30)
        ctr_of = lambda dl: [first, (second[0], second[1], second[2] + dl)]
        good = d0
        assert seq_ok(ctr_of(d0), 2)[0]
        dl = d0
        while base + dl - 120 >= 30:
            if not seq_ok(ctr_of(dl - 120), 2)[0]:
                break
            dl -= 120
            good = dl
        dl = good - 30
        while base + dl >= 30 and seq_ok(ctr_of(dl), 2)[0]:
            good = dl
            dl -= 30
        best = (good, ctr_of(good))
        delta, ctr = best
        print(' %s then %s: smallest spacing found: second control delayed by %d against its natural time, i.e. the %s salvo reaches B_0 %d generations after the %s salvo (30 generations less fails, or the gap would drop below 30)' % (
            fn, sn, delta, sn, base + delta, fn))
        print('    controls %s and %s' % (wlname(ctr[0]), wlname(ctr[1])))
        for k in (0, 2, 4, 40):
            ok, n, box = seq_ok(ctr, k)
            assert ok, k
            print('    k = %2d: evolve %d (R ∪ C ∪ C\' ∪ B_k) = R ∪ B_k: checked; box x %d..%d, y %d..%d' % (k, n, box[0], box[2], box[1], box[3]))



if __name__ == '__main__':
    main()
