#!/usr/bin/env python3
"""Z4 (R-25): exact feasibility of a PSG1-type supply for the alternative decision design of
z2_detector.py (test salvo A1, A2 on one SW lane 30 apart, B 4 lanes away; detector D annihilated
by A1 when k >= 1).  Equations only, no simulation.

Work in the mirror frame M = sym 4, (x, y) -> (-x, y): there the test gliders fly SE (as the
salvos of PG1 / PSG1) and D' flies SW.  Supply plan (as g7_push.py, R-23):
  C_U -> U (fan-out, SE output = core control C0, SW output = continue glider)   -> D' directly
  core S + K: path 1  G1 (NW) -> RF1 -> SW leg (lane m) -> RF2 -> SE              -> B'
              path 2  G2 (SW) -> multi-release gate Gb (2 stream gliders, 30 apart) -> RF3 -> A1', A2'
Invariants (asserted): tau + 4 lane of B' depends only on m (I_a(m), g7_push.invariant_a);
tau - 4 lane of the continue glider does not depend on u (I_d); the rigid four-glider target has
the translation invariant J = (tau_D' - 4 L_D') - (tau_B' + 4 L_B').  Exact condition:
I_a(m) = I_d - J for some m in the leg range, with the lane parities; and the insertion rule for
the A' pair next to B' (net.insertion_clear).
Usage: z4_feasible.py > results/z4_feasible.txt     (run from any directory)
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LM = os.path.join(HERE, '..', 'life_machine')
sys.path.insert(0, LM)
os.chdir(LM)                       # g7_push reads its inputs relative to scripts/life_machine (read only)
from common import SE, SW, NE, NW, DIRNAME, life          # noqa: E402
from reactions import sym_wl                              # noqa: E402
from machine import load_catalog                          # noqa: E402
from net import insertion_clear                           # noqa: E402
import g7_push as g7                                      # noqa: E402


def wl(w):
    return '(%s, %d, %d)' % (DIRNAME[w[0]], w[1], w[2])


def main():
    A1, A2, B = (SW, 12, 0), (SW, 12, 30), (SW, 8, 53)
    txt = open(os.path.join(HERE, 'results', 'z2_detector.txt')).read()
    Ds = sorted(set((int(a), int(b)) for a, b in re.findall(r'killer 0 D \(SE, (-?\d+), (-?\d+)\)', txt)))
    print('design salvo (frame SlidingBlock.lean, SW):', wl(A1), wl(A2), wl(B), '; detector options (killer A1): %d' % len(Ds))
    m = {w: sym_wl(w, 4) for w in (A1, A2, B)}
    A1m, A2m, Bm = m[A1], m[A2], m[B]
    print('mirror frame M: A1\' %s A2\' %s B\' %s' % (wl(A1m), wl(A2m), wl(Bm)))
    for order, (out, others) in (('B\' first, then A\' pair', (A1m, [Bm])),):
        r1 = insertion_clear((A1m[1], A1m[2]), [(Bm[1], Bm[2])])
        r2 = insertion_clear((A2m[1], A2m[2]), [(Bm[1], Bm[2])])
        print('  insertion of A1\', A2\' beside B\' (B\' inserted first):', r1, r2)
        r3 = insertion_clear((Bm[1], Bm[2]), [(A1m[1], A1m[2]), (A2m[1], A2m[2])])
        print('  insertion of B\' beside A1\', A2\' (A\' pair first):', r3)
    # multi-release gates whose control can be G2 (SW) and whose outputs fly NE or SW
    recs = load_catalog()
    cnt = {}
    for r in recs:
        if r['kind'] == 'other' and r['from_infinity'] and r.get('verified') and len(r['outs']) == 2:
            nm = [x[1] for x in r['outs']]
            w = sorted(x[0] for x in r['outs'])
            if nm[0] == nm[1] and nm[0] in 'AB' and w[0][:2] == w[1][:2] and w[1][2] - w[0][2] == 30:
                for k in range(8):
                    if life.sym_apply(k, r['d']) == SW:
                        od = life.sym_apply(k, w[0][0])
                        cnt[DIRNAME[od]] = cnt.get(DIRNAME[od], 0) + 1
    print('two-glider multi-release gates (30 apart), control turned to SW, output direction:', cnt)
    core, ups = g7.load_fanouts()
    print('core fan-outs (NW + SW outputs): %d; upstream fan-outs (SE + SW outputs): %d' % (len(core), len(ups)))
    Id = {}
    for j, fu in enumerate(ups):
        vals = set()
        for u in (-150, -151, -200, -201):
            c = g7.place_U(fu, u)[3]
            vals.add((c[2] - 4 * c[1], c[1] % 2 if u % 2 == 0 else (c[1] + 1) % 2))
        assert len(set(v[0] for v in vals)) == 1, vals
        Id.setdefault(vals.pop()[0], []).append(j)
    print('I_d = tau - 4 lane of the continue glider (independent of u), values:', sorted(Id))
    Ia = []
    for ci, fc in enumerate(core):
        d, par = g7.invariant_a(fc)
        Ia.append((d, par))
    sols = []
    for (Ld, td) in Ds:
        Dm = sym_wl((SE, Ld, td), 4)
        J = (Dm[2] - 4 * Dm[1]) - (Bm[2] + 4 * Bm[1])
        for idv, js in Id.items():
            for ci, (d, par) in enumerate(Ia):
                for mm, ia in d.items():
                    if ia == idv - J:
                        sols.append(((Ld, td), J, idv, ci, mm, js[0]))
    print('exact (m, core, U) solutions of I_a(m) = I_d - J over all detector options: %d' % len(sols))
    seen = set()
    for s in sols:
        if s[0] in seen:
            continue
        seen.add(s[0])
        print('  D (SE, %d, %d): J %d, I_d %d, core %d, m %d, U %d' % (s[0][0], s[0][1], s[1], s[2], s[3], s[4], s[5]))
        if len(seen) >= 25:
            break
    print('detector options with at least one solution: %d of %d' % (len(set(s[0] for s in sols)), len(Ds)))


if __name__ == '__main__':
    main()
