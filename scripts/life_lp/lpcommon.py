#!/usr/bin/env python3
"""Shared code of scripts/life_lp (R-31, untrusted oracle; numerical observations only).
Imports read-only: scripts/life_layout (R-30), scripts/life_route (R-29), life_machine, life_zero,
life_gates.  Coordinates (u, v) = (x - y, x + y) as in R-30."""
import os
import sys

LPHERE = os.path.dirname(os.path.abspath(__file__))
LAY = os.path.join(LPHERE, '..', 'life_layout')
if LAY not in sys.path:
    sys.path.insert(0, LAY)
from lcommon import *  # noqa
import l2_layout as L2  # noqa
import l0_module  # noqa
import l1_parts  # noqa

LPRES = os.path.join(LPHERE, 'results')
coord_of, lane_of, is_u = L2.coord_of, L2.lane_of, L2.is_u


def tuv(w, u, v):
    """Time at which the glider w passes the (u, v) point (on its line)."""
    return time_at(w, ((u + v) / 2, (v - u) / 2))


def route(g, turns):
    """R-30's route() but every coordinate must already have the right parity (asserted)."""
    for (d, c) in turns:
        pass
    pieces, corners, legs = [], [], [g]
    for (d, c) in turns:
        assert (c + coord_of(legs[-1])) % 2 == 1, ('parity', legs[-1], d, c)
        r = reflect(legs[-1], d, lane_of(d, c))
        assert r is not None
        rf, g2 = r
        a = coord_of(legs[-1])
        corners.append((a, c) if is_u(legs[-1][0]) else (c, a))
        pieces.append(rf)
        legs.append(g2)
    return pieces, legs[-1], corners, legs
