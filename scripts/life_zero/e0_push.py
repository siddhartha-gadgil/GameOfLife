#!/usr/bin/env python3
"""E0 (R-27): REG1's push salvo (frame of counter 0: (SE,-10,1034), (SE,1,983), (SE,8,1010)) against
the products of the four detectors (d0_single.py): what does one push (or two) leave?"""
from dcat import *
from common import lean_window
from recipes import settle
from common import step_cells

PUSH = [(SE, -10, 1034), (SE, 1, 983), (SE, 8, 1010)]
DETS = [(SW, 9, 0), (SW, 10, 0), (NE, -10, 0), (NE, -11, 0)]


def x_of(det):
    st, t, rest, gl = run_free([det], extra=counter(-1), t0=-200, max_gen=800, max_pop=300, max_span=150)
    return set(rest)


def push_on(X, n=1, gap=300):
    gl = []
    for i in range(n):
        gl += [shift_wl(w, 0, 0, i * gap) for w in PUSH]
    st, t, rest, out = run_free(gl, extra=X, t0=800, max_gen=3000, max_pop=400, max_span=200)
    return st, rest, out


if __name__ == '__main__':
    for k in (-1, 0, 1):
        st, rest, out = push_on(set(counter(k)))
        print('push on counter %d:' % k, st, lean_window(set(rest)) if rest else '', out)
    for det in DETS:
        X = x_of(det)
        for n in (1, 2):
            st, rest, out = push_on(X, n)
            print('detector', DIRNAME[det[0]], det[1], 'X', lean_window(X), '+ %d push(es):' % n, st,
                  lean_window(set(rest)) if rest else 'empty', [(DIRNAME[w[0]],) + w[1:] for w in (out or [])])
