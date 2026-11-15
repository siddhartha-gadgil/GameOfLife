#!/usr/bin/env python3
"""G2 (R-29): reuse spacings of the register REG1 + DZ2 (R-28), exact simulation (gsim, unbounded
plane with escaping gliders peeled off).  Two control gliders, the second one delayed by 30 m:

  DD  : C', then C' + 30 m          (DEC after DEC; after NZ when k >= 1, after Z when k = 0)
  II  : C_I, then C_I + 30 m        (INC after INC)
  DI  : C', then C_I + 30 m         (INC after DEC)
  ID  : C_I, then C' + 30 m         (DEC after INC)

C' = (SE, 41, 4444) (DZ2's control), C_I = REG1's INC control (SE, 314, -2222 + 30 n0).  C_I is
inserted as a free glider on its lane *downstream of DZ2's reflector RF_C3* (which emits DZ2's own
C_I on lane 314; an INC control from the far NW on lane 314 would hit RF_C3 - see g3_lane314.py).
Expected end state: cycle ∪ B_(final k) and exactly the expected output gliders, nothing else.
Usage: g2_reuse.py CASE K M0 M1 [STEP]   (prints one line per m)"""
import sys
from multiprocessing import Pool
from gcommon import *

PIECES, D = dz2()
CP = D['ctrl']                         # (SE, 41, 4444)
CI0 = (SE, 314, -2222 + 30 * 200)      # REG1's INC control (phase of R-24), tau 3778
CBOX = core_box(PIECES, [(140, 230, 900, 900)])
CI_POINT = (-700, -1014)               # C_I is inserted near here (lane 314, downstream of RF_C3 (-876, -1175))


def dec(k, w):
    """DZ2 run by the control w on B_k: (new k, outputs, end time)."""
    s = w[2] - CP[2]
    if k == 0:
        return 0, [shift_wl(D['zout'], 0, 0, s)], w[2] + 22796
    return k - 1, [shift_wl(D['n1'], 0, 0, s)], w[2] + 6746


def inc(k, w):
    return k + 1, [], w[2] + 3212 + 4 * k + 200


def case_controls(case, m):
    if case == 'DD':
        return [('D', CP), ('D', shift_wl(CP, 0, 0, 30 * m))]
    if case == 'II':
        return [('I', CI0), ('I', shift_wl(CI0, 0, 0, 30 * m))]
    if case == 'DI':
        return [('D', CP), ('I', (SE, 314, -2222 + 30 * m))]
    if case == 'ID':
        return [('I', CI0), ('D', (SE, 41, 4444 + 30 * m))]
    raise ValueError(case)


def insert_time(w):
    if w[1] == 314:
        return 30 * (int(time_at(w, CI_POINT)) // 30)
    return 30 * ((int(time_at(w, (-1100, -1100))) - 400) // 30)


def one(args):
    case, k, m = args
    ctr = case_controls(case, m)
    kk, outs, tend = k, [], 0
    for typ, w in ctr:
        kk, o, te = (dec if typ == 'D' else inc)(kk, w)
        outs += o
        tend = max(tend, te)
    tend = 30 * ((tend + 300 + 29) // 30)
    starts = sorted((insert_time(w), w) for typ, w in ctr)
    t = starts[0][0]
    cells = state(PIECES, [starts[0][1]], t, block(k))
    removed = []
    pending = starts[1:]
    from life import chebyshev_dist
    while True:
        tnext = pending[0][0] if pending else tend
        if tnext > t:
            cells, rem = run_peel([], [], t, tnext, extra=cells, cbox=CBOX)
            removed += rem
            t = tnext
        if not pending:
            break
        ts, w = pending.pop(0)
        g = glider_at(*w, t)
        if chebyshev_dist(g, cells) < 4:
            return (case, k, m, ctr[1][1][2], 'insert-conflict')
        cells |= g
    want = state(PIECES, [], t, block(kk))
    ok = cells == want and sorted(removed) == sorted(outs)
    msg = 'ok' if ok else 'FAIL extra %d missing %d removed %s expected %s' % (
        len(cells - want), len(want - cells), [wl(x) for x in sorted(removed)], [wl(x) for x in sorted(outs)])
    return (case, k, m, 'second control tau %d' % ctr[1][1][2], msg)


def main():
    case, k, m0, m1 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    step = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    jobs = [(case, k, m) for m in range(m0, m1 + 1, step)]
    with Pool(int(os.environ.get('G2_PROCS', '16'))) as P:
        for r in P.imap(one, jobs):
            print(*r, flush=True)


if __name__ == '__main__':
    main()
