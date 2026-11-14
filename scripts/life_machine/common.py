#!/usr/bin/env python3
"""Common code of scripts/life_machine (untrusted oracle; numerical observations only).

Reuses, read-only, the simulator and the gate code of scripts/life_gates (life.py, gates.py).

Conventions (those of the Lean project and of life_gates):
  * a cell is (x, y), x to the right, y DOWNWARD;
  * a window (x0, y0, rows): bit j of rows[i] (least significant bit = leftmost) is (x0 + j, y0 + i);
  * a glider world line is (d, lane, tau), d = (dx, dy) the direction: at the times t = tau (mod 4)
    the glider is the canonical glider S_d with bounding box origin (x, y),
    lane = dy * x - dx * y,  tau = t - 4 * dx * x   (life.glider_at, life.glider_worldline).

`python3 common.py` runs the cross-checks against LeanTheory/Theory/Life/{Guns,Gates,SlidingBlock}.lean.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_gates'))

import life                                                      # noqa: E402
import gates                                                     # noqa: E402
from life import (cells_of_window, window_of_cells, bbox, translate, transform, step_cells,   # noqa: E402,F401
                  evolve_cells, components, glider_worldline, glider_at, lean_window, show, Board,
                  sym_apply, SYMS, GUN, EATER1)

SE, SW, NW, NE = (1, 1), (-1, 1), (-1, -1), (1, -1)
DIRNAME = {SE: 'SE', SW: 'SW', NW: 'NW', NE: 'NE'}

# --- data of the Lean files -------------------------------------------------------------------
BLOCKED_STREAM = frozenset(cells_of_window(0, 0, [
    16777216, 73786976294859177984, 368934881525733797888, 455118177873004657149952,
    644012837187738926121987, 1858139645101047596242387971, 1858223245745189647925969920,
    1227889072522402593802240, 642241841670271749074944, 453347182355485948903424,
    147573952589726744576, 110680464442282475520, 221360928884514619392, 0, 0, 0, 0, 5368709120,
    1441151887201009664, 864691130602618880, 576460752303423488, 0, 0, 0, 274877906944,
    4505248894812160, 3378524354248704, 6755399441055744]))          # Gates.lean `blockedStream`
GUN_B = frozenset(cells_of_window(55, 1, [2048, 10240, 12632067, 17874947, 51573735424,
                                          51576055808, 34080768, 17825792, 12582912]))
GATE_CONTROL = frozenset(cells_of_window(47, 6, [2, 4, 7]))
GATE_OUTPUT = frozenset(cells_of_window(45, 32, [5, 6, 2]))
PULL_SALVO = frozenset(cells_of_window(0, 5, [2, 4, 647, 768, 256]))
PUSH_SALVO = frozenset(cells_of_window(0, 0, [4, 8, 14, 0, 0, 2, 4, 647, 768, 256]))
# world lines of the salvo gliders at time 0 (computed in cross_check and asserted there)
PULL_WL = [(SE, -5, 0), (SE, 1, -29)]
PUSH_WL = [(SE, -5, 0), (SE, 1, -29), (SE, 1, -4)]


def counter(k):
    """SlidingBlock.lean `counter k`: the block with upper left cell (7 + k, 11 + k)."""
    return frozenset(cells_of_window(7 + k, 11 + k, [3, 3]))


def worldlines_of(cells, t=0):
    """World lines of a set of cells that consists of free gliders only (else None)."""
    out = []
    for comp in components(cells, 2):
        wl = glider_worldline(comp, t)
        if wl is None:
            return None
        out.append(wl)
    return sorted(out)


def gliders_at(wls, t):
    c = set()
    for wl in wls:
        c |= glider_at(*wl, t)
    return c


def cross_check():
    # Guns.lean (through life.self_test)
    life.self_test()
    # Gates.lean: blockedStream_start, blockedStream_isOscillator, gate
    assert evolve_cells(set(GUN) | set(GUN_B), 90) == set(BLOCKED_STREAM)
    c = set(BLOCKED_STREAM)
    for q in range(1, 31):
        c = step_cells(c)
        assert (c == set(BLOCKED_STREAM)) == (q == 30), q
    assert evolve_cells(set(BLOCKED_STREAM) | set(GATE_CONTROL), 90) == set(BLOCKED_STREAM) | set(GATE_OUTPUT)
    R = gates.Reference.blocked(4, 90, 1, 0)
    assert set(R.ref_cells[0]) == set(BLOCKED_STREAM) and R.tref == 90
    print('Gates.lean: evolve 90 (gosperGun ∪ gunB) = blockedStream; least period 30;')
    print('  evolve 90 (blockedStream ∪ ofRows 47 6 [2,4,7]) = blockedStream ∪ ofRows 45 32 [5,6,2]: checked')
    # SlidingBlock.lean: pull, push for k = 0 .. 5
    for k in range(6):
        assert evolve_cells(set(PULL_SALVO) | set(counter(k)), 4 * k + 26) == set(counter(k - 1))
        assert evolve_cells(set(PUSH_SALVO) | set(counter(k)), 4 * k + 32) == set(counter(k + 1))
    assert worldlines_of(PULL_SALVO) == sorted(PULL_WL)
    assert worldlines_of(PUSH_SALVO) == sorted(PUSH_WL)
    print('SlidingBlock.lean: pull and push checked for k = 0 .. 5;')
    print('  pullSalvo = gliders', PULL_WL)
    print('  pushSalvo = gliders', PUSH_WL)


if __name__ == '__main__':
    cross_check()
