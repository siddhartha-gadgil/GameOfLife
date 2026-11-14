#!/usr/bin/env python3
"""X1: when can a reflector insert an SE glider next to a parallel SE glider already in flight?

For the output (SE, 0, 0) of a copy of RF0 (input from NE or from SW) and one other SE glider on
lane -d (input NE) or +d (input SW), d = 4 .. 20, delay dt = -80 .. 80: does everything fly on
unchanged (net.insertion_ok, set simulator)?  'P' = yes.  The rule net.insertion_clear is read
off this table.  (Lanes nearer than 4, and the near side, never pass: R-21, 3.1.)

Usage: x1_insertion.py > results/x1_insertion.txt      (about 10 min, one process)
"""
from common import SE, SW, NE, DIRNAME
from net import insertion_ok

out = (SE, 0, 0)
for din, sgn in ((NE, -1), (SW, 1)):
    for dl in (4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16, 20):
        row = ''.join('P' if insertion_ok(out, din, [(SE, sgn * dl, dt)]) else '.' for dt in range(-80, 81))
        print('input %s, other lane %+d, dt -80..80: %s' % (DIRNAME[din], sgn * dl, row), flush=True)
