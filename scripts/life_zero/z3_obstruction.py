#!/usr/bin/env python3
"""Z3 (R-25): the two geometric obstructions to supplying `zeroTestInput` (ZeroTestLogic.lean)
with the components of R-21 .. R-23 (gun gates, the reflector RF0, free-glider collisions).

  (O1) T1 = (SW, 12, 24) and T3 = (SW, 10, 50) are parallel, 2 lanes apart.
  (O2) nzOut flies NW 2 lanes beside the detector's lane, i.e. back along the path on which the
       detector came: it meets whatever emitted the detector.

This script decodes the Lean windows, prints the world lines and the lane offsets, and re-checks
the facts used (set simulator, unbounded plane):
  * zeroTest_decision for k = 0, 1, 2, 3, 40 (196 generations), as a cross-check of the frame;
  * the head-on window: two antiparallel gliders interact for every timing iff their lane offset
    is in -5 .. 7 (results/z0_headon.txt);
  * RF0 passing scan summary (results/z0_rfpass.txt): idle reflector + one glider on a lane parallel
    or antiparallel to its output lane, all 120 relative phases.
Usage: z3_obstruction.py > results/z3_obstruction.txt
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import (cells_of_window, counter, components, glider_worldline, evolve_cells, SE, SW, NW, NE,  # noqa: E402
                    DIRNAME, glider_at)

ZT_INPUT = (-27, -6, [5, 6, 2, 0, 1099511627776, 5497558138880, 3307124817920, 4294967296, 30064771072,
                      0, 0, 0, 17179869184, 8589934592, 60129542144])
ZEATERS = (-46, 51, [12, 8, 7, 1, 0, 0, 0, 12, 8, 7, 1])
ZOUT = (22, 43, [5, 6, 2])
NZOUT = (-35, -14, [2, 3, 5])


def W(w):
    return set(cells_of_window(*w))


def wl(w):
    return '(%s, lane %d, tau %d)' % (DIRNAME[w[0]], w[1], w[2])


def main():
    X = W(ZT_INPUT)
    gl = sorted(glider_worldline(c, 0) for c in components(X, 2))
    print('zeroTestInput (time 0) = 4 gliders:', ', '.join(wl(g) for g in gl))
    E = W(ZEATERS)
    z = glider_worldline(W(ZOUT), 196)
    nz = glider_worldline(W(NZOUT), 196)
    print('zOut  at time 196:', wl(z))
    print('nzOut at time 196:', wl(nz))
    for k in (0, 1, 2, 3, 40):
        end = evolve_cells(X | E | set(counter(k)), 196)
        exp = E | set(counter(k)) | (W(ZOUT) if k == 0 else W(NZOUT))
        assert end == exp, k
    print('zeroTest_decision re-checked for k = 0, 1, 2, 3, 40 (evolve 196): ok')
    sw = [g for g in gl if g[0] == SW]
    D = [g for g in gl if g[0] == SE][0]
    print('\n(O1) SW test gliders, lanes:', sorted(g[1] for g in sw),
          '-> pairwise lane offsets', sorted(abs(a[1] - b[1]) for i, a in enumerate(sw) for b in sw[:i]))
    # SE-lane of the NW glider nz: the NW lane is -x + y, the SE lane x - y
    c = glider_at(*nz, 196)
    xs = min(x for x, y in c)
    ys = min(y for x, y in c)
    # compare cell sets: offset of the lines x - y of the two gliders' cells
    cD = glider_at(*D, 0)
    off = (sum(x - y for x, y in c) / len(c)) - (sum(x - y for x, y in cD) / len(cD))
    print('(O2) detector D = %s; nzOut = %s; mean (x - y) of the cells: nzOut - D = %+.1f;'
          ' in the lane coordinates of z0_rfpass (SE lane of a NW glider = -its NW lane): %+d' % (
              wl(D), wl(nz), off, -nz[1] - D[1]))
    print('     nzOut flies NW, i.e. back along the path on which D came, 2 lanes beside it.')
    hp = os.path.join(HERE, 'results', 'z0_headon.txt')
    if os.path.exists(hp):
        bad = [int(m.group(1)) for m in re.finditer(r'NW lane\s+([+-]?\d+) .*: tau 0..15 \.+', open(hp).read())]
        print('\nhead-on SE (0,0) + NW (lane, tau): interaction for every tau iff NW lane in', min(bad), '..', max(bad),
              '(%d lanes); all other lanes pass for every tau' % len(bad))
    rp = os.path.join(HERE, 'results', 'z0_rfpass.txt')
    if os.path.exists(rp):
        print('\nRF0 idle, one glider passing (120 relative phases each); offsets that pass for all/none:')
        for line in open(rp):
            m = re.match(r'input (\w+); passing (\w+), lane offset\s+([+-]?\d+) from the (\w+) lane:\s+(\d+)/120', line)
            if m and m.group(4) == 'out':
                pass
        rows = {}
        for line in open(rp):
            m = re.match(r'input (\w+); passing (\w+), lane offset\s+([+-]?\d+) from the (\w+) lane:\s+(\d+)/120', line)
            if m:
                key = (m.group(1), m.group(2), m.group(4))
                rows.setdefault(key, []).append((int(m.group(3)), int(m.group(5))))
        for key, v in rows.items():
            ok = [o for o, n in v if n == 120]
            part = [o for o, n in v if 0 < n < 120]
            print('  input %s, passing %s, offsets -10..10 from the %s lane: pass always %s; sometimes %s' % (
                key[0], key[1], key[2], ok if ok else 'none', part if part else 'none'))


if __name__ == '__main__':
    main()
