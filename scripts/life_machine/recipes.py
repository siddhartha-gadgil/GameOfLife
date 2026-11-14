#!/usr/bin/env python3
"""Free-glider recipes: collisions of a few gliders that leave exactly a prescribed set of gliders.

Purpose (report R-21): a salvo glider that is not the direct output of a gate has to be *inserted*
on its lane by a collision taking place in front of all guns.  This module provides
  * `settle`  : evolve a small configuration until it is a still life / period-2 oscillator plus
                gliders that provably never meet anything again;
  * `place`   : put a glider on a given lane just before a settled constellation;
  * the tree search of r1_recipes.py is built on these.
"""
from common import (step_cells, bbox, components, glider_worldline, glider_at, SE, SW, NW, NE)

VEL = {SE: (1, 1), SW: (-1, 1), NW: (-1, -1), NE: (1, -1)}


def _sep_forever(b1, v1, b2, v2, gap=4):
    """Boxes b = (x0, y0, x1, y1) moving with velocities v (cells per 4 generations): is there a
    coordinate in which they are at least `gap` apart and do not approach?"""
    for ax in (0, 1):
        lo1, hi1, lo2, hi2 = b1[ax], b1[ax + 2], b2[ax], b2[ax + 2]
        if lo2 - hi1 >= gap and v2[ax] - v1[ax] >= 0:
            return True
        if lo1 - hi2 >= gap and v1[ax] - v2[ax] >= 0:
            return True
    return False


def settle(cells, t0=0, max_gen=800, max_pop=120, max_span=90):
    """Evolve from time t0.  Returns (status, t, rest, gliders):
      'settled' : at time t the configuration is `rest` (period 1 or 2; cells at time t) plus the
                  gliders with world lines `gliders`, and no two of these objects can ever meet;
      'fail'    : not settled within the limits."""
    cells = set(cells)
    t = t0
    hist = {}
    while t - t0 <= max_gen:
        if (t - t0) % 4 == 0:
            if not cells:
                return ('settled', t, frozenset(), [])
            if len(cells) > max_pop:
                return ('fail', t, None, None)
            comps = components(cells, 2)
            gl = []
            rest = set()
            for comp in comps:
                wl = glider_worldline(comp, t)
                if wl is None:
                    rest |= comp
                else:
                    gl.append((wl, bbox(comp)))
            if rest:
                rb = bbox(rest)
                if rb[2] - rb[0] > max_span or rb[3] - rb[1] > max_span:
                    return ('fail', t, None, None)
            # is the rest stable (period 1 or 2)?
            stable = True
            if rest:
                r2 = step_cells(step_cells(rest))
                stable = (r2 == rest)
            if stable:
                objs = [(b, VEL[wl[0]]) for (wl, b) in gl]
                if rest:
                    # dilate the rest box by 1: a period-2 oscillator may be one cell larger
                    objs.append(((rb[0] - 1, rb[1] - 1, rb[2] + 1, rb[3] + 1), (0, 0)))
                ok = True
                for i in range(len(objs)):
                    for j in range(i + 1, len(objs)):
                        if not _sep_forever(objs[i][0], objs[i][1], objs[j][0], objs[j][1]):
                            ok = False
                            break
                    if not ok:
                        break
                if ok:
                    return ('settled', t, frozenset(rest), sorted(wl for (wl, b) in gl))
        cells = step_cells(cells)
        t += 1
    return ('fail', t, None, None)


def glider_box(d, lane, q):
    """Bounding box of the canonical glider with parameter q (x = dx q)."""
    x = d[0] * q
    y = d[0] * (d[1] * x - lane)
    return (x, y, x + 2, y + 2)


def _cheb_box(a, b):
    dx = max(a[0] - b[2], b[0] - a[2], 0)
    dy = max(a[1] - b[3], b[1] - a[3], 0)
    return max(dx, dy)


def place(box, d, lane, t, tau_mod=0, modulus=1, margin=5):
    """A world line (d, lane, tau), tau = tau_mod (mod modulus), of a glider that at time t has not
    yet come within Chebyshev distance `margin` of the box (and neither did before), chosen as
    late as possible.  Returns None if the lane never comes within distance 2 of the box."""
    # parameters q at which the canonical glider is within distance < margin of the box
    span = (box[2] - box[0]) + (box[3] - box[1]) + 4 * margin + 20
    cx = (box[0] + box[2]) // 2
    q_mid = d[0] * cx
    near = [q for q in range(q_mid - span, q_mid + span + 1)
            if _cheb_box(glider_box(d, lane, q), box) < margin]
    hit = [q for q in near if _cheb_box(glider_box(d, lane, q), box) <= 2]
    if not hit:
        return None
    q0 = min(near) - 1                      # last parameter before coming near
    # at time t the glider must have parameter floor((t - tau) / 4) <= q0  (4 phases after S_d)
    tau = t - 4 * q0 - 3
    tau += (tau_mod - tau) % modulus
    return (d, lane, tau)
