#!/usr/bin/env python3
"""G6 (R-29): exact simulation of the merge chain of g5_chain.py (results/g5_chain.json).
(1) chain alone: each input (T into G_1 from the far NW; S into each G_i from the far SW, residues
    1..13 and +30 m) gives back the chain plus exactly one glider (SE, 41, tau = 4444 mod 30);
(2) chain + DZ2 + REG1 (R-28), one input, block B_k: the end state is the cycle of everything plus
    the expected block and exactly the DZ2 output (k = 0: Z, k >= 1: NZ), nothing else.
Usage: g6_chain_sim.py [ks]"""
import sys
import json
from gcommon import *
from net import wl_out
from common import components, glider_worldline

C = json.load(open(os.path.join(RES, 'g5_chain.json')))
GATES = [tuple(g) for g in C['gates']]
T_IN = (SE, 43, 5)
PIECES, D = dz2()
CP = D['ctrl']


def gl_list(cells, t):
    out = []
    for comp in components(cells, 2):
        g = glider_worldline(comp, t)
        if g is None:
            return None
        out.append(g)
    return sorted(out)


def inputs():
    """(name, world line, gate index) of every input, at a late enough time."""
    res = []
    w = wl_out(T_IN, GATES[0])
    res.append(('T into G_1', w, 0))
    for i, g in enumerate(GATES):
        for r in (1, 7, 13):
            res.append(('S into G_%d residue %d' % (i + 1, r), wl_out((NE, -76, r), g), i))
    return res


def start_time(w, gi, back=200):
    g = GATES[gi]
    t = time_at(w, (g[2] + 45, g[3] + 31)) - back
    return 30 * (int(t) // 30)


def alone():
    for name, w, gi in inputs():
        t0 = start_time(w, gi)
        t1 = t0 + 30 * 40
        c, _ = run(GATES, [w], t0, t1)
        rest = c - state(GATES, [], t1)
        miss = state(GATES, [], t1) - c
        gl = gl_list(rest, t1)
        ok = not miss and gl is not None and len(gl) == 1 and gl[0][:2] == (SE, 41) and (gl[0][2] - CP[2]) % 30 == 0
        print('  chain alone, %-22s %s -> %s: %s' % (name, wl(w), [wl(x) for x in gl] if gl else gl, 'ok' if ok else 'FAIL'), flush=True)


def with_dz2(ks):
    allp = PIECES + GATES
    cbox = core_box(allp, [(140, 230, 900, 900)])
    for name, w, gi in inputs():
        if 'residue 1' in name or 'residue 13' in name:
            continue
        # chain output time for this input
        t0 = start_time(w, gi)
        c, _ = run(GATES, [w], t0, t0 + 1200)
        out = gl_list(c - state(GATES, [], t0 + 1200), t0 + 1200)[0]
        delay = out[2] - CP[2]
        for k in ks:
            t1 = 30 * ((delay + (27540 if k == 0 else 11490) - 300 + 300) // 30 + 1)
            cells, rem = run_peel(allp, [w], t0, t1, extra=block(k), cbox=cbox)
            o = shift_wl(D['zout'] if k == 0 else D['n1'], 0, 0, delay)
            want = state(allp, [], t1, block(k - 1 if k else 0))
            ok = cells == want and rem == [o]
            print("  chain + DZ2, %-22s k = %d: C' = %s, output %s: %s (evolve %d)" % (
                name, k, wl(out), wl(o), 'ok' if ok else 'FAIL %s' % [wl(x) for x in rem], t1 - t0), flush=True)


if __name__ == '__main__':
    print('chain: %s' % (GATES,))
    alone()
    with_dz2([int(a) for a in (sys.argv[1] if len(sys.argv) > 1 else '0,1,2').split(',')])
