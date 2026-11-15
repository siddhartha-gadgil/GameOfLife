#!/usr/bin/env python3
"""G14 (R-29): the shared register, all components together, exact simulation.
Pieces: REG1 + DZ2' (DZ2 with RF_C3 -> RF_C3', g10/g11) + G_I + RF_J + INC merge chain (g12, 3 copies)
+ DEC merge chain (g5, 3 copies) + dispatch stations on the NZ and Z lines (g9, 2 + 2) + eaters.
 DEC: control into any input of the DEC chain (T into G_1, S into G_1..G_3), with the tokens of a
      calling instruction j (NZ token + Z token, delayed with C'):
        k = 0 -> B_0 and exactly the glider dispatched at Z station j;
        k >= 1 -> B_(k-1) and exactly the glider dispatched at NZ station j.
 INC: control into any input of the INC chain: B_k -> B_(k+1), nothing else.
Usage: g14_full.py [ks] [which: dec,inc]"""
import sys
import json
from gcommon import *
from net import wl_out, env_cells
from life import sym_apply
import g11_inc_check as G11

T = lambda w: (tuple(w[0]), w[1], w[2])
base, GI, RFC3, CI = G11.design(0)
DECC = [tuple(g) for g in json.load(open(os.path.join(RES, 'g5_chain.json')))['gates']]
INC = json.load(open(os.path.join(RES, 'g12_inc_chain.json')))[0]
INCC = [tuple(g) for g in INC['gates']]
RFJ = tuple(INC['RF_J'])
DSP = json.load(open(os.path.join(RES, 'g9_dispatch.json')))
STATIONS = [tuple(p) for p in DSP['pieces']]
EATERS = {tuple(c) for c in DSP['eaters']}
PIECES = base + [RFJ] + INCC + DECC + STATIONS
_, D = dz2()
CP = D['ctrl']


def chain_inputs(gates):
    res = [('T into copy 1', wl_out((SE, 43, 5), gates[0]), gates[0])]
    for i, g in enumerate(gates):
        res.append(('S into copy %d' % (i + 1), wl_out((NE, -76, 7), g), g))
    return res


def ins_time(w, g, back=250):
    c = sym_apply(g[1], (45, 31))
    return 30 * ((int(time_at(w, (c[0] + g[2], c[1] + g[3]))) - back) // 30)


def chain_output_delay(gates, w, target):
    """Delay (multiple of 30) of the chain's final output for input w relative to `target`."""
    t0 = ins_time(w, [g for g in gates if True][0])
    t0 = min(ins_time(w, g) for g in gates)
    c, _ = run(gates, [w], t0, t0 + 2400)
    from common import components, glider_worldline
    rest = c - state(gates, [], t0 + 2400)
    out = glider_worldline(rest, t0 + 2400)
    assert out is not None and out[:2] == target[:2], out
    return out[2] - target[2]


def main():
    ks = [int(a) for a in (sys.argv[1] if len(sys.argv) > 1 else '0,1,2,40').split(',')]
    which = (sys.argv[2] if len(sys.argv) > 2 else 'dec,inc').split(',')
    print('pieces: %d (REG1 22 + DZ2\' 19 + G_I, RF_J + INC chain 3 + DEC chain 3 + stations 8); eaters %d cells' % (len(PIECES), len(EATERS)))
    cbox = core_box(PIECES, [(140, 230, 900, 900), bbox(EATERS)])
    if 'dec' in which:
        for name, w, g in chain_inputs(DECC):
            # add 30 m so that everything starts after time 0
            w = shift_wl(w, 0, 0, 30 * 100)
            delay = chain_output_delay(DECC, w, CP)
            for k in ks:
                for caller in (0, 1):
                    evs = [(min(ins_time(w, gg) for gg in DECC if True), w)]
                    evs = [(ins_time(w, g), w)]
                    for st in (DSP['nz'][caller], DSP['z'][caller]):
                        gst = tuple(st[0])
                        K = shift_wl(T(st[2]), 0, 0, delay)
                        evs.append((ins_time(K, gst), K))
                    t0 = min(e[0] for e in evs)
                    t_end = 30 * (max([CP[2] + delay - 4444 - 300 + (27540 if k == 0 else 11490)] + [e[0] for e in evs]) // 30) + 1800
                    cells, rem = run_events(state(PIECES, [], t0, EATERS | block(k)), t0, evs, t_end, cbox)
                    want = state(PIECES, [], t_end, EATERS | block(k - 1 if k else 0))
                    exp = [shift_wl(T((DSP['z'] if k == 0 else DSP['nz'])[caller][3]), 0, 0, delay)]
                    ok = cells == want and rem == exp
                    print('  DEC %-14s %s (C\' delayed by %d), k = %d, caller %d: -> %s %s' % (
                        name, wl(w), delay, k, caller, [wl(x) for x in rem], 'ok' if ok else 'FAIL'), flush=True)
    if 'inc' in which:
        for name, w, g in chain_inputs(INCC):
            w = shift_wl(w, 0, 0, 30 * 100)
            for k in ks + ([3] if 3 not in ks else []):
                t0 = ins_time(w, g)
                t_end = t0 + 30 * ((9000 + 4 * k) // 30)
                cells, rem = run_events(state(PIECES, [w], t0, EATERS | block(k)), t0, [], t_end, cbox)
                want = state(PIECES, [], t_end, EATERS | block(k + 1))
                print('  INC %-14s %s, k = %d: -> B_%d %s' % (name, wl(w), k, k + 1, 'ok' if (cells == want and not rem) else 'FAIL %s' % rem), flush=True)


if __name__ == '__main__':
    main()
