#!/usr/bin/env python3
"""Cell-exact data (project window convention, ready for Lean as `ofRows x0 y0 [rows]`) for the
recommended designs of report R-20, each statement re-checked with the set simulator on the
unbounded plane (`life.step_cells`), independently of the bit-parallel board used in the searches.

Usage:
    report_data.py eater ORIENT EX EY
    report_data.py blocked K DX DY P
    report_data.py gate K DX DY P  DIRX DIRY LANE TAU  [M ...]      (extra control gliders 30 M later)
    report_data.py series K DX DY P  VX VY  DIRX DIRY LANE TAU
"""
import sys

import life
import gates
from life import (GUN, EATER1, bbox, transform, normalize, translate, evolve_cells, step_cells,
                  lean_window, components, glider_worldline, glider_at, show)


def pr(name, cells):
    b = bbox(cells)
    print('  %-28s %s   -- %d cells, box x %d..%d, y %d..%d' % (name + ':', lean_window(cells), len(cells), b[0], b[2], b[1], b[3]))


def eater(k, ex, ey):
    e = translate(normalize(transform(EATER1, k)), ex, ey)
    c = set(GUN) | e
    print('Terminated gun: gun + eater (orientation %d) at (%d, %d)' % (k, ex, ey))
    pr('gun', GUN)
    pr('eater', e)
    pr('whole (generation 0)', c)
    hist = [c]
    for t in range(3030):
        hist.append(step_cells(hist[-1]))
    t0 = 3000
    while t0 > 0 and hist[t0 - 1] == hist[t0 - 1 + 30]:
        t0 -= 1
    assert all(hist[t] == hist[t + 30] for t in range(t0, 3001))
    assert all(hist[t0] != hist[t0 + q] for q in range(1, 30))
    print('  checked: state(t) = state(t + 30) for %d <= t <= 3000, least period 30; transient %d' % (t0, t0))
    tref = ((t0 + 29) // 30) * 30
    env = bbox(set().union(*hist[tref:tref + 30]))
    print('  envelope over a cycle: x %d..%d, y %d..%d' % (env[0], env[2], env[1], env[3]))
    if t0 > 0:
        pr('periodic at generation %d' % tref, hist[tref])
        rest = hist[tref] - set(GUN) - e
        for comp in components(rest, 2):
            pr('  glider in flight', comp)
    print(show(hist[tref]))


def describe_cycle(R, label='R0', guns=()):
    """guns: list of (name, cells) of gun bodies expected inside the configuration."""
    c0 = set(R.ref_cells[0])
    pr(label + ' (whole)', c0)
    rest = set(c0)
    for name, g in guns:
        assert g <= c0, name
        pr('  ' + name, g)
        rest -= g
    for comp in sorted(components(rest, 2), key=lambda c: bbox(c)):
        wl = glider_worldline(comp, 0)
        if wl is not None:
            pr('  glider %s lane %d tau %d' % (wl[0], wl[1], wl[2]), comp)
        else:
            pr('  part (%d cells)' % len(comp), comp)
    e = R.env
    print('  envelope over a cycle: x %d..%d, y %d..%d  (%d x %d)' % (e[0], e[2], e[1], e[3], e[2] - e[0] + 1, e[3] - e[1] + 1))
    print('  streams (direction, lane, tau mod 30):', R.streams)


def gun_parts(k, dx, dy, p, tref, v=(0, 0), tag=''):
    pA, pB = gates.phases(p)
    qa, qb = (tref + pA) % 30, (tref + pB) % 30
    A = translate(life.gun_phase(qa), *v)
    B = translate(translate(transform(life.gun_phase(qb), k), dx, dy), *v)
    return [('gun A%s (gun at generation %d)' % (tag, qa), A),
            ('gun B%s (sym_%d of the gun at generation %d)' % (tag, k, qb), B)]


def blocked(k, dx, dy, p):
    pA, pB = gates.phases(p)
    A = gates.gun_at(pA)
    B = translate(transform(gates.gun_at(pB), k), dx, dy)
    print('Blocked stream (k, dx, dy, p) = (%d, %d, %d, %d)' % (k, dx, dy, p))
    print(' initial configuration (generation 0): gun A at generation %d of its cycle, gun B = sym_%d of the gun at generation %d, translated by (%d, %d)' % (pA, k, pB, dx, dy))
    pr('gun A', A)
    pr('gun B', B)
    pr('whole (generation 0)', A | B)
    R = gates.Reference.blocked(k, dx, dy, p)
    # independent check with the set simulator
    c = A | B
    hist = [c]
    for t in range(R.tref + 30):
        hist.append(step_cells(hist[-1]))
    assert hist[R.tref] == R.ref_cells[0] and hist[R.tref + 30] == hist[R.tref]
    t0 = R.tref
    while t0 > 0 and hist[t0 - 1] == hist[t0 - 1 + 30]:
        t0 -= 1
    assert t0 == R.transient
    assert all(hist[R.tref] != hist[R.tref + q] for q in range(1, 30))
    print(' transient %d (state(t) = state(t + 30) exactly from generation %d on; least period 30)' % (t0, t0))
    print(' periodic configuration R0 at the reference generation tref = %d (set simulator: evolve %d of the initial configuration = R0, evolve 30 R0 = R0)' % (R.tref, R.tref))
    describe_cycle(R, 'R0', gun_parts(k, dx, dy, p, R.tref))
    print(show(R.ref_cells[0]))
    return R


def gate_statement(R, wls, label):
    """Find T (multiple of 30) at which all control gliders are free, and the first multiple of 30
    after the return to the cycle; print and check the statement."""
    b = R.board
    ivs, t_in, t_out = gates.free_intervals(R, *wls[0])
    t_ins = ivs[0][1]
    res = gates.run_gate(R, wls, t_ins, limit=3000)
    assert res['status'] == 'restored', res['status']
    tb = gates.back_time(R, res, t_ins)
    outs = [w for (w, th) in res['out']]
    T = 30 * (t_ins // 30)
    while True:
        try:
            ok = all(not (b.of_cells(glider_at(*wl, T)) & R.refdil[0]) for wl in wls)
        except ValueError:
            ok = False
        if ok:
            break
        T -= 30
        assert T > t_ins - 600
    Te = 30 * ((tb + 29) // 30)
    N = Te - T
    start = set(R.ref_cells[0])
    for wl in wls:
        start |= glider_at(*wl, T)
    end = set(R.ref_cells[0])
    for wl in outs:
        g = glider_at(*wl, Te)
        assert life.chebyshev_dist(g, R.ref_cells[0]) >= 3
        end |= g
    assert evolve_cells(start, N) == end
    print(' %s' % label)
    print('  gate times: control gliders free until %d, interaction, back in the cycle (with the released gliders in free flight) from %d on: %d generations' % (t_ins, tb, tb - t_ins))
    print('  statement checked with the set simulator:  evolve %d (R0 ∪ C) = R0 ∪ G   (start = gate time %d, end = gate time %d, both ≡ 0 mod 30)' % (N, T, Te))
    for i, wl in enumerate(wls):
        pr('C%d  %s lane %d tau %d' % (i + 1, wl[0], wl[1], wl[2]), glider_at(*wl, T))
    for i, wl in enumerate(outs):
        pr('G%d  %s lane %d tau %d %s' % (i + 1, wl[0], wl[1], wl[2], R.stream_name(wl) or 'X'), glider_at(*wl, Te))
    pr('start R0 ∪ C', start)
    pr('end R0 ∪ G', end)
    return start, end, N


def main():
    a = sys.argv[1:]
    if a[0] == 'eater':
        eater(int(a[1]), int(a[2]), int(a[3]))
    elif a[0] == 'blocked':
        blocked(*[int(x) for x in a[1:5]])
    elif a[0] == 'gate':
        v = [int(x) for x in a[1:]]
        R = blocked(*v[:4])
        wl = ((v[4], v[5]), v[6], v[7])
        wls = [wl] + [(wl[0], wl[1], wl[2] + 30 * m) for m in v[8:]]
        gate_statement(R, wls, 'Gate: control glider(s) %s' % (wls,))
    elif a[0] == 'series':
        v = [int(x) for x in a[1:]]
        R = gates.Reference.blocked(*v[:4])
        vx, vy = v[4], v[5]
        wl = ((v[6], v[7]), v[8], v[9])
        RC = gates.Reference(set(R.ref_cells[0]) | translate(R.ref_cells[0], vx, vy))
        print('Two gates in series: blocked stream %s and its translate by (%d, %d)' % (v[:4], vx, vy))
        describe_cycle(RC, 'R0 ∪ translate R0', gun_parts(*v[:4], R.tref) + gun_parts(*v[:4], R.tref, (vx, vy), "'"))
        s, e, N = gate_statement(RC, [wl], 'Series: control glider %s for gate 1' % (wl,))
        print(show(s))


if __name__ == '__main__':
    main()
