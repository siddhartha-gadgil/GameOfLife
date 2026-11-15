#!/usr/bin/env python3
"""G0 (R-29): all collisions of two gliders X = (SE, 0, 0) and T (SW / NE / NW), outcome classes.
Lists every collision whose settled result is exactly one glider (any direction) and nothing else,
and those with one glider plus a small still life.  Own enumeration (set simulator)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NE, NW, DIRNAME, glider_at
from reactions import run_free
from collections import Counter

X = (SE, 0, 0)
seen = set()
res = Counter()
one = []
for dT in (SW, NE, NW):
    lanes = range(-12, 13) if dT == NW else (0, 1)
    for L in lanes:
        for tau in range(-60, 61):
            T = (dT, L, tau)
            st, t, rest, gl = run_free([X, T], t0=-200, max_gen=1200, max_pop=300, max_span=120)
            if st != 'settled':
                res['fail'] += 1
                continue
            if sorted(gl) == sorted([X, T]):
                res['no interaction'] += 1
                continue
            key = (len(gl), len(rest))
            res[key] += 1
            if len(gl) == 1 and len(rest) <= 8:
                one.append((T, gl, len(rest)))
print(res)
for T, gl, nr in one:
    print('T', DIRNAME[T[0]], T[1], T[2], '->', [(DIRNAME[w[0]], w[1], w[2]) for w in gl], 'rest cells', nr)
