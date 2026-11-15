#!/usr/bin/env python3
"""G1 (R-29): re-run R-28's complete DZ2 checks (f8_full.py) with the fast simulator gsim:
   k >= 1: cycle ∪ C' ∪ B_k -> cycle ∪ B_(k-1) ∪ NZ  (evolve 11490 from world time Ts)
   k = 0 : cycle ∪ C' ∪ B_0 -> cycle ∪ B_0 ∪ Z       (evolve 27540)
Also measures, for k = 0, the world time at which the block is back at B_0 for good (last change
of the cells around the register diagonal) - the 'restore end'."""
import sys, time
from gcommon import *


def main():
    pieces, d = dz2()
    Ts = 30 * ((int(time_at(d['ctrl'], (-1100, -1100))) - 400) // 30)
    print("DZ2: %d pieces; C' %s; NZ %s; Z %s; Ts = %d" % (len(pieces), wl(d['ctrl']), wl(d['n1']), wl(d['zout']), Ts))
    ks = [int(a) for a in (sys.argv[1].split(',') if len(sys.argv) > 1 else '0,1,2,3,40,100'.split(','))]
    for k in ks:
        t0 = time.time()
        N = 27540 if k == 0 else 11490
        out = d['zout'] if k == 0 else d['n1']
        c, box = run(pieces, [d['ctrl']], Ts, Ts + N, extra=block(k))
        want = state(pieces, [out], Ts + N, block(k - 1 if k else 0))
        print('  k = %3d: evolve %d = cycle ∪ B_%d ∪ %s: %s  (run box x %d..%d, y %d..%d; %.0f s)' % (
            k, N, k - 1 if k else 0, 'Z' if k == 0 else 'NZ', 'checked' if c == want else 'FAILS',
            box[0], box[2], box[1], box[3], time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
