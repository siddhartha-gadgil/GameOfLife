#!/usr/bin/env python3
"""D5 (R-26): two-glider restore units (catalogue d4, closed under symmetry) that take the
detector's product X back to counter 0 and whose gliders each pass every block counter k >= 0.
For each: the NZ case counter k + U1 + U2 (k = 0 .. 6, 40) and the Z case
counter (-1) + D + U (unit delayed by s after the detector)."""
from dcat import *

DET = {'SW9': ((SW, 9, 0), (7, 8), (0, 3)), 'NE-10': ((NE, -10, 0), (4, 11), (3, 0))}


def show(w):
    return '(%s, %d, %d)' % (DIRNAME[w[0]], w[1], w[2])


if __name__ == '__main__':
    U = load_units()
    for name, (D, X, need) in DET.items():
        for u in U:
            if u[2] != need or u[3]:
                continue
            v = move_unit(u, X[0], X[1], 0)
            if not (harmless(v[0]) and harmless(v[1])):
                continue
            print('detector', name, show(D), 'unit', show(v[0]), show(v[1]))
            t0 = int(min(time_at(v[0], X), time_at(v[1], X))) - 60
            for k in list(range(0, 7)) + [40]:
                st, t, rest, gl = run_free([v[0], v[1]], extra=counter(k), t0=t0 - 4 * k, max_gen=1500, max_pop=300, max_span=150)
                ok = st == 'settled' and set(rest) == set(counter(k))
                print('   NZ k=%d: %s block kept %s gliders %s' % (k, st, ok, [show(w) for w in (gl or [])]))
            tD = time_at(D, (6, 10))
            good = []
            for s in range(-40, 200):
                w = move_unit(v, 0, 0, s)
                t0 = int(min(tD, time_at(w[0], X), time_at(w[1], X))) - 60
                st, t, rest, gl = run_free([D, w[0], w[1]], extra=counter(-1), t0=t0, max_gen=1500, max_pop=300, max_span=150)
                if st == 'settled' and set(rest) == set(counter(0)) and not gl:
                    good.append(s)
            print('   Z: counter(-1) + D + unit delayed by s -> counter 0 for s in', good[:5], '...', good[-3:], len(good))
