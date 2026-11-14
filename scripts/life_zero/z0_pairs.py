#!/usr/bin/env python3
"""Z0 (R-25): all collisions of two free gliders, SE (0, 0) + d2 (lane, tau), that leave only
gliders (no debris).  Own enumeration with the set simulator of scripts/life_gates (imported).
Usage: z0_pairs.py > results/z0_pairs.txt"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NW, NE, DIRNAME, glider_at
from reactions import run_free

def main():
    res = []
    for d2 in (SW, NW):
        for lane in range(-14, 15):
            for tau in range(-60, 61):
                ins = [(SE, 0, 0), (d2, lane, tau)]
                st, t, rest, gl = run_free(ins, t0=-200, max_gen=1200)
                if st != 'settled':
                    continue
                if sorted(gl) == sorted(ins):
                    continue
                if rest:
                    continue
                res.append((DIRNAME[d2], lane, tau, [(DIRNAME[w[0]], w[1], w[2]) for w in gl]))
                print(res[-1], flush=True)
    json.dump(res, open(os.path.join(HERE, 'results', 'z0_pairs.json'), 'w'))

if __name__ == '__main__':
    main()
