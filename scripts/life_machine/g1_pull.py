#!/usr/bin/env python3
"""Search G1: pull-salvo generator = round-trip fan-out (f2_roundtrip.py) + one reflector.

Pieces:
  S, K : the two assemblies of a verified fan-out (results/f2_roundtrip.json.gz).  One control
         glider C0 = (SE, 41, 22) into S gives G1 (stream glider of K) and G2 (stream B glider of
         S, flying SW).
  RF   : the period-30 reflector of q1_reflector.py (queen bee shuttle of the gun + eater),
         RF0 = ofRows 0 2 [12288, 34816, 66563, 214019, 66560, 1607680, 2633728, 2097152, 6291456],
         which turns (SW, 19, 18) into (NW, -14, 13) [times = cycle time of RF0, mod 30].
One of G1, G2 is used directly as a salvo glider, the other one is turned by a copy of RF
(symmetry k, translation (p, q), delay s) onto the lane of the second salvo glider.  The pull
salvo is {(SE, l, t), (SE, l + 6, t - 29)}.  The position of RF along the incoming lane is the
only freedom, and  tau + 4 lane  of the outgoing glider does not depend on it, so a fan-out fits
only if one exact equation holds; all verified fan-outs and both roles are tried.

Every fit is simulated: composite (S, K, RF) periodic with period 30; with C0 it returns to its
cycle and exactly the two salvo gliders leave (board, then set simulator on the unbounded plane);
then with the block `counter k` (suitably translated), k = 0 .. 3.

Usage: g1_pull.py        Output: results/g1_pull.json.gz, summary on stdout
"""
import gzip
import json
import os
import time

from common import (cells_of_window, glider_at, glider_worldline, transform, translate, bbox, SE, SW,
                    NW, NE, DIRNAME, gates, life, step_cells, counter, evolve_cells)
import machine
from machine import asm_cells, asm_envelope, box_dist, run_scheduled, verify_scheduled
from reactions import shift_wl, sym_wl

RF0 = frozenset(cells_of_window(0, 2, [12288, 34816, 66563, 214019, 66560, 1607680, 2633728, 2097152, 6291456]))
RF_IN = (SW, 19, 18)
RF_OUT = (NW, -14, 13)
C0 = (SE, 41, 22)
S_ASM = (0, 0, 0, 0)

_rf_cycle = None


def rf_cycle():
    global _rf_cycle
    if _rf_cycle is None:
        c = [set(RF0)]
        for _ in range(29):
            c.append(step_cells(c[-1]))
        assert step_cells(c[-1]) == c[0]
        _rf_cycle = [frozenset(x) for x in c]
    return _rf_cycle


def rf_cells(rf, t):
    k, p, q, s = rf
    return translate(transform(rf_cycle()[(t - s) % 30], k), p, q)


def rf_fit(g_in, target):
    """Reflector placements (k, p, q, s) turning the glider g_in into exactly `target`."""
    out = []
    for k in range(8):
        i0, o0 = sym_wl(RF_IN, k), sym_wl(RF_OUT, k)
        if i0[0] != g_in[0] or o0[0] != target[0]:
            continue
        di, do = i0[0], o0[0]
        # lanes: d[1] p - d[0] q
        # di[1] p - di[0] q = g_in.lane - i0.lane ; do[1] p - do[0] q = target.lane - o0.lane
        a1, b1, c1 = di[1], -di[0], g_in[1] - i0[1]
        a2, b2, c2 = do[1], -do[0], target[1] - o0[1]
        det = a1 * b2 - a2 * b1
        pn, qn = c1 * b2 - c2 * b1, a1 * c2 - a2 * c1
        if det == 0 or pn % det or qn % det:
            continue
        p, q = pn // det, qn // det
        s = g_in[2] - i0[2] + 4 * di[0] * p              # exact delay making the input fit
        o = shift_wl(o0, p, q, s)
        assert shift_wl(i0, p, q, s) == g_in
        if o == target:
            out.append((k, p, q, s % 30))
    return out


class Comp:
    def __init__(self, cells, margin=20):
        self.R = gates.Reference(cells, margin)


def try_fit(fo, role):
    """fo: a fan-out record; role 0: G1 direct, G2 reflected; role 1: G2 direct?? (not SE) --
    only the SE glider can be direct, so role selects which salvo glider the direct one is."""
    asm = tuple(fo['asm'])
    outs = [(tuple(o[0]), o[1], o[2]) for o in fo['outs']]
    direct = [w for w in outs if w[0] == SE]
    other = [w for w in outs if w[0] != SE]
    if len(direct) != 1 or len(other) != 1:
        return []
    g, h = direct[0], other[0]
    if role == 0:        # g = a (lane l), reflected = b = (l + 6, t - 29)
        target = (SE, g[1] + 6, g[2] - 29)
        a, b = g, target
    else:                # g = b, reflected = a = (l - 6, t + 29)
        target = (SE, g[1] - 6, g[2] + 29)
        a, b = target, g
    res = []
    for m in range(0, 40):
        # the same fan-out one or more periods later gives h delayed by 30 m and g by 30 m as
        # well, which is no new freedom; so m = 0 only.
        if m:
            break
        for rf in rf_fit(h, target):
            res.append((rf, a, b))
    return res


def verify(fo, rf, a, b):
    asm = tuple(fo['asm'])
    cS, cK, cR = asm_cells(S_ASM, 0), asm_cells(asm, 0), rf_cells(rf, 0)
    if (cS | cK) & cR:
        return 'overlap', None
    try:
        comp = Comp(set(cS) | set(cK) | set(cR))
    except AssertionError:
        return 'not periodic', None
    res = run_scheduled(comp, [C0], limit=8000, t_hint=200)
    if res['status'] != 'restored':
        return res['status'], None
    outs = sorted(w for (w, th) in res['out'])
    if outs != sorted([a, b]):
        return 'other gliders %s' % (outs,), None
    ok, Ts, Te = verify_scheduled(comp, [C0], res)
    if not ok:
        return 'verification failed', None
    return 'ok', (comp, Ts, Te)


def main():
    t = time.time()
    d = json.load(gzip.open('results/f2_roundtrip.json.gz', 'rt'))
    fits = []
    for fo in d['good']:
        for role in (0, 1):
            for (rf, a, b) in try_fit(fo, role):
                fits.append((fo, role, rf, a, b))
    print('fan-outs: %d; exact fits of one reflector: %d' % (len(d['good']), len(fits)))
    good = []
    for (fo, role, rf, a, b) in fits:
        st, extra = verify(fo, rf, a, b)
        print('  K asm %s role %d reflector %s -> a=%s b=%s : %s' % (tuple(fo['asm']), role, rf, a[1:], b[1:], st))
        if st == 'ok':
            good.append({'asm': fo['asm'], 'role': role, 'rf': list(rf), 'a': [list(a[0]), a[1], a[2]],
                         'b': [list(b[0]), b[1], b[2]], 'Ts': extra[1], 'Te': extra[2]})
    with gzip.open('results/g1_pull.json.gz', 'wt') as f:
        json.dump(good, f)
    print('verified pull generators: %d (%.0f s)' % (len(good), time.time() - t))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
