#!/usr/bin/env python3
"""Shared code of scripts/life_layout (R-30, untrusted oracle; numerical observations only).

Imports read-only: scripts/life_route (gsim, gcommon: DZ2', REG1, OR gate, chains, stations),
scripts/life_zero, scripts/life_machine, scripts/life_gates.

Coordinates: world frame of REG1, cells (x, y), y down.  Rotated coordinates u = x - y, v = x + y:
an SE / NW glider keeps u (its SE lane), v grows / falls by 2 per diagonal step; an NE / SW glider
keeps v (= minus its NE lane), u grows / falls by 2 per step.  A glider covers 2 units of (u, v)
per 4 generations.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROUTE = os.path.join(HERE, '..', 'life_route')
for p in (ROUTE, os.path.join(HERE, '..', 'life_machine'), os.path.join(HERE, '..', 'life_zero'),
          os.path.join(HERE, '..', 'life_gates')):
    if p not in sys.path:
        sys.path.append(p)

from gcommon import *  # noqa
from net import wl_out, wl_in, reflect, reflect_to, env_cells, env_box, box_dist, set_dist, compose, RF_TURN  # noqa
from life import sym_apply  # noqa

LHERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(LHERE, 'results')      # (gcommon's star import rebinds HERE)
DIRS = {'SE': SE, 'SW': SW, 'NW': NW, 'NE': NE}


def uv(p):
    return (p[0] - p[1], p[0] + p[1])


def xy(u, v):
    assert (u + v) % 2 == 0
    return ((u + v) // 2, (v - u) // 2)


def T(w):
    return (tuple(w[0]), w[1], w[2])


def move(p, dx, dy, s=0):
    """Piece translated by (dx, dy) and delayed by s."""
    return (p[0], p[1], p[2] + dx, p[3] + dy, (p[4] + s) % 30)


def mwl(w, dx, dy, s=0):
    return shift_wl(w, dx, dy, s)


def cross(g):
    """Crossing point of an assembly piece (image of (45, 31))."""
    c = sym_apply(g[1], (45, 31))
    return (c[0] + g[2], c[1] + g[3])


def wl_point_time(w, pt):
    return time_at(w, pt)


def pos_at(w, t):
    """Approximate position (x, y) of the glider w at time t (bounding box origin)."""
    d, lane, tau = w
    q = (t - tau) // 4
    x = d[0] * q
    y = d[0] * (d[1] * x - lane)
    return (x, y)
