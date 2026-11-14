#!/usr/bin/env python3
"""Z0b (R-25): head-on pairs SE (0, 0) + NW (lane, tau): for which lane offsets do they pass each
other unchanged for every relative timing?  Usage: z0_headon.py > results/z0_headon.txt"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, NW, glider_at
from reactions import run_free

for lane in range(-12, 13):
    row = ''
    for tau in range(0, 16):
        ins = [(SE, 0, 0), (NW, lane, tau)]
        st, t, rest, gl = run_free(ins, t0=-200, max_gen=1000)
        row += 'P' if (st == 'settled' and not rest and sorted(gl) == sorted(ins)) else '.'
    print('NW lane %+3d (SE-lane of the NW glider %+3d): tau 0..15 %s' % (lane, -lane, row), flush=True)
