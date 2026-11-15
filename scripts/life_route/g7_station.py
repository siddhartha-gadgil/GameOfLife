#!/usr/bin/env python3
"""G7 (R-29): DISPATCH station, gate coordinates (blockedStream = gate G, phase 0).

Obstruction (g0_pairs.py): every collision of two gliders that leaves exactly one glider is a
kickback (or the head-on side step); its output flies back within 2 lanes of the line of one of the
two inputs.  Station design: the token K releases the gate's gun-B glider T = (SW, 75, .); T meets
the returning register output X at the point P, D diagonal steps beyond the gate's crossing; the
kickback output Y flies back along T's line (+2, 0 or -2 lanes) into the gate, where it is a
repeatable control that releases the gun-A glider S = (SE, 14, .): the dispatched glider.
Without X, T flies on (to an absorber); without T, X passes far from the gate.

For every variant and D: Y's line and residue, the check against the gate catalogue, and the exact
simulation  gate + K + X -> gate + S,  gate + K -> gate + T,  gate + X -> gate + X.
Usage: g7_station.py [K_lane K_tau]   (default K = (SW, 46, 5): releases T = (SW, 75, 111))"""
import sys
import json
from gcommon import *
from reactions import images, fit, run_free
from common import components, glider_worldline

G = ('asm', 0, 0, 0, 0)
TPL1 = ([(SE, 0, 0), (SW, 0, 17)], [(NE, -2, 5)])     # g0_pairs.py: output back beside T's line
TPL2 = ([(SE, 0, 0), (NE, 0, 17)], [(SW, 0, 5)])      # output back on T's line


def check_templates():
    for tpl in (TPL1, TPL2):
        st, t, rest, gl = run_free(tpl[0], t0=-100, max_gen=600)
        assert st == 'settled' and not rest and gl == tpl[1], (tpl, gl)


def gl_list(cells, t):
    out = []
    for comp in components(cells, 2):
        g = glider_worldline(comp, t)
        if g is None:
            return None
        out.append(g)
    return sorted(out)


def sim(gliders, t0, n=None, t1=None):
    t1 = t1 if t1 is not None else t0 + n
    c, _ = run([G], gliders, t0, t1, box=(-1200, -1200, 1300, 1300), margin=100)
    base = state([G], [], t1)
    if base - c:
        return None
    return gl_list(c - base, t1)


def variants(T):
    """(name, X, Y) for every image of the two templates in which T is the SW glider and the
    output flies NE (back towards the gate); j = position of P along T's line."""
    out = []
    for ti, tpl in enumerate((TPL1, TPL2)):
        for k, im in enumerate(images(tpl)):
            ins, outs = im
            for i in range(2):
                if ins[i][0] == SW and outs[0][0] == NE:
                    out.append(('TPL%d sym%d' % (ti + 1, k), im, i))
    return out


def main():
    check_templates()
    KL, KT = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (46, 5)
    K = (SW, KL, KT + 300)
    tK = int(time_at(K, (45, 31)))
    r = sim([K], 30 * ((tK - 150) // 30), 600)
    T = r[0]
    print('K = %s releases %s' % (wl(K), [wl(x) for x in r]))
    res = []
    for name, im, i in variants(T):
        for j in range(-400, 401):
            ins, outs = fit(im, i, T, j)
            X = ins[1 - i]
            Y = outs[0]
            Lx = X[1] if X[0] == SE else -X[1]          # x - y on X's line
            D = round(45 - (75 + Lx) / 2)               # diagonal steps from the crossing to P
            if D < 20 or D > 120:
                continue
            res.append((name, D, X, Y))
    print('%d variant positions with D in 20..120' % len(res))
    good = []
    for name, D, X, Y in sorted(res, key=lambda r: (r[1], r[0])):
        t0 = 30 * ((tK - 150) // 30)
        rKX = sim([K, X], t0, t1=30 * ((int(time_at(X, (45, 31))) + 8 * D + 700) // 30))
        ok = rKX is not None and len(rKX) == 1 and rKX[0][:2] == (SE, 14)
        line = '%s D=%d X=%s Y=%s : K+X -> %s' % (name, D, wl(X), wl(Y), [wl(x) for x in rKX] if rKX else rKX)
        if ok:
            rX = sim([X], 30 * ((int(time_at(X, (45, 31))) - 8 * D - 300) // 30), 30 * ((16 * D + 600) // 30))
            okX = rX is not None and len(rX) == 1 and rX[0] == X
            line += '; X alone passes: %s' % okX
            ok = ok and okX
            if ok:
                good.append({'variant': name, 'D': D, 'K': K, 'T': T, 'X': X, 'Y': Y, 'S': rKX[0]})
        print(line, flush=True)
    json.dump(good, open(os.path.join(RES, 'g7_station.json'), 'w'))
    print('stations: %d' % len(good))


if __name__ == '__main__':
    main()
