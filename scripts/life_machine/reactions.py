#!/usr/bin/env python3
"""Elementary free-glider reactions as templates on world lines, with their symmetric images.

A template is (inputs, outputs): lists of world lines.  `images(tpl)` gives its 8 symmetric
images; `fit(tpl, i, wl, j)` translates a template in space and time so that its input number i
becomes the world line wl; the remaining freedom (the position along wl) is the integer j.

Templates (each re-checked by simulation in `python3 reactions.py`):
  KICK : SE (0, 0) + SW (6, 7)  ->  NW (life.py lane 2, tau 12)        (R-19 "R3", kickback)
  SIDE : SE (0, 0) + NW (life.py lane -4, tau 18)  ->  SE (6, -13)     (R-19 "R3'", head-on)
"""
from common import (glider_at, glider_worldline, transform, translate, step_cells, SE, SW, NW, NE,
                    DIRNAME, worldlines_of)
from recipes import settle

KICK = ([(SE, 0, 0), (SW, 6, 7)], [(NW, 2, 12)])
SIDE = ([(SE, 0, 0), (NW, -4, 18)], [(SE, 6, -13)])


def shift_wl(wl, p, q, s):
    """World line after translation by (p, q) and delay by s generations."""
    d, lane, tau = wl
    return (d, lane + d[1] * p - d[0] * q, tau + s - 4 * d[0] * p)


def sym_wl(wl, k):
    return glider_worldline(transform(glider_at(*wl, 0), k), 0)


def images(tpl):
    return [([sym_wl(w, k) for w in tpl[0]], [sym_wl(w, k) for w in tpl[1]]) for k in range(8)]


def fit(tpl, i, wl, j=0):
    """Translate the template so that input i is exactly wl; j slides it along wl."""
    d, lane0, tau0 = tpl[0][i]
    assert d == wl[0]
    L = wl[1] - lane0
    p = L * d[1] + j * d[0]
    q = j * d[1]
    s = wl[2] - tau0 + 4 * d[0] * p
    return ([shift_wl(w, p, q, s) for w in tpl[0]], [shift_wl(w, p, q, s) for w in tpl[1]])


def run_free(wls, extra=(), t0=None, max_gen=3000, max_pop=400, max_span=400):
    """Evolve free gliders (world lines) plus still cells `extra` from a time at which all gliders
    are pairwise far apart; returns settle's result (status, t, rest, gliders)."""
    if t0 is None:
        t0 = min(w[2] for w in wls) - 400
    cells = set(extra)
    for w in wls:
        cells |= glider_at(*w, t0)
    return settle(cells, t0, max_gen=max_gen, max_pop=max_pop, max_span=max_span)


def check_templates():
    for name, tpl in (('KICK', KICK), ('SIDE', SIDE)):
        for k, im in enumerate(images(tpl)):
            for j in (0, 3):
                ins, outs = fit(im, 0, shift_wl(im[0][0], 5, -2, 7), j)
                t0 = min(w[2] for w in ins) - 40
                st, t, rest, gl = run_free(ins, t0=t0)
                assert st == 'settled' and not rest and sorted(gl) == sorted(outs), (name, k, j, gl, outs)
        print(name, 'checked in 8 orientations:',
              ' + '.join('%s(%d, %d)' % (DIRNAME[w[0]], w[1], w[2]) for w in tpl[0]), '->',
              ' + '.join('%s(%d, %d)' % (DIRNAME[w[0]], w[1], w[2]) for w in tpl[1]))


if __name__ == '__main__':
    check_templates()
    # table of the kickback in its 8 orientations
    print('kickback images (main glider, kicker -> returned glider):')
    for im in images(KICK):
        print('  ', [(DIRNAME[w[0]], w[1], w[2]) for w in im[0]], '->', [(DIRNAME[w[0]], w[1], w[2]) for w in im[1]])
    print('side step images:')
    for im in images(SIDE):
        print('  ', [(DIRNAME[w[0]], w[1], w[2]) for w in im[0]], '->', [(DIRNAME[w[0]], w[1], w[2]) for w in im[1]])
