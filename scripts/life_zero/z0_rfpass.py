#!/usr/bin/env python3
"""Z0c (R-25): can a glider pass an IDLE reflector RF0 (no input) on a lane parallel or
antiparallel to its output lane (or to its input lane), at small lane offsets?  All 120 relative
phases (30 phases of the reflector x 4 phases of the glider) are tried, set simulator.

The reflector is the copy of RF0 that emits (SE, 0, 0) from an input flying `din`; the passing
glider flies `dpass` on the lane at offset `off` from the output lane (dpass in {SE, NW}) or from
the input lane (dpass in {din, -din}), in the lane coordinates of dpass.
Usage: z0_rfpass.py > results/z0_rfpass.txt"""
import os
import sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NE, NW, DIRNAME                       # noqa: E402
from net import reflect_to, rf_point, time_at, free_run, expect  # noqa: E402

NEG = {SE: NW, NW: SE, SW: NE, NE: SW}


def job(a):
    din, rel, dpass, off = a
    rf, gin = reflect_to((SE, 0, 0), din, 0)
    pt = rf_point(rf)
    base = (SE, 0, 0) if rel == 'out' else gin
    # lane of a parallel line at offset `off` in the coordinates of dpass
    lane = base[1] + off if dpass == base[0] else -(base[1] + off)
    row = ''
    for ph in range(120):
        g = (dpass, lane, ph)
        tc = int(time_at(g, pt))
        t0 = tc - 200
        end = free_run([rf], [g], t0, 400)
        row += 'P' if end == expect([rf], [g], t0 + 400) else '.'
    return a, row


if __name__ == '__main__':
    jobs = []
    for din in (NE, SW):
        for dp in (SE, NW):
            jobs += [(din, 'out', dp, off) for off in range(-10, 11)]
        for dp in (din, NEG[din]):
            jobs += [(din, 'in', dp, off) for off in range(-10, 11)]
    with Pool(8) as p:
        for (din, rel, dp, off), row in p.imap(job, jobs):
            print('input %s; passing %s, lane offset %+3d from the %s lane: %3d/120 %s' % (
                DIRNAME[din], DIRNAME[dp], off, rel, row.count('P'), row), flush=True)
