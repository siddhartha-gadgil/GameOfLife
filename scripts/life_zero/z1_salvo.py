#!/usr/bin/env python3
"""Z1 (R-25): unconditional zero-test salvos that a reflector network can supply.

Frame of SlidingBlock.lean (block at position k = counter k).  Three SW gliders
  A1 = (SW, a, 0), A2 = (SW, a, 30 m), B = (SW, b, tb)
two on the same lane a (30 m generations apart: one reflector or one gate serves both) and one on
a lane b with |a - b| >= 4 (a reflector can insert it beside the others).  Wanted (as R7 of R-19):
  * block at 0: all three gliders are destroyed and the block is left at 0 (nothing else);
  * block at k = 1 .. KMAX: the three gliders pass unchanged (they never touch the block).
Lanes a, b in LANES (SW lanes that pass every block k >= 1 are <= 12), m in 1 .. 4,
tb in TB.  Set simulator (scripts/life_machine/reactions.run_free, imported).

Usage: [Z1_LO=.. Z1_HI=.. Z1_GAP=.. Z1_OUT=..] z1_salvo.py > results/z1_salvo.txt   (writes results/$Z1_OUT)
"""
import json
import os
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SW, counter                                   # noqa: E402
from reactions import run_free                                   # noqa: E402

LANES = range(int(os.environ.get('Z1_LO', -4)), int(os.environ.get('Z1_HI', 12)) + 1)
MINGAP = int(os.environ.get('Z1_GAP', 4))
OUT = os.environ.get('Z1_OUT', 'z1_salvo.json')
TB = range(-160, 281)
KMAX = 12


def restores(wls):
    t0 = min(w[2] for w in wls) - 160
    st, t, rest, gl = run_free(wls, extra=counter(0), t0=t0, max_gen=900)
    return st == 'settled' and rest == counter(0) and not gl


def passes(wls):
    t0 = min(w[2] for w in wls) - 160
    for k in range(1, KMAX + 1):
        st, t, rest, gl = run_free(wls, extra=counter(k), t0=t0, max_gen=900)
        if not (st == 'settled' and rest == counter(k) and sorted(gl) == sorted(wls)):
            return False
    return True


def job(arg):
    a, b, m = arg
    out = []
    for tb in TB:
        wls = [(SW, a, 0), (SW, a, 30 * m), (SW, b, tb)]
        if restores(wls) and passes(wls):
            out.append(wls)
    return arg, out


def main():
    jobs = [(a, b, m) for a in LANES for b in LANES if abs(a - b) >= MINGAP for m in (1, 2, 3, 4)]
    found = []
    with Pool(8) as p:
        for arg, out in p.imap_unordered(job, jobs):
            for w in out:
                print('found: lanes a %d (taus 0, %d), b %d (tau %d)' % (arg[0], 30 * arg[2], arg[1], w[2][2]), flush=True)
            found += out
    print('jobs %d, found %d' % (len(jobs), len(found)))
    json.dump(found, open(os.path.join(HERE, 'results', OUT), 'w'))


if __name__ == '__main__':
    main()
