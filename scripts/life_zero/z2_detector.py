#!/usr/bin/env python3
"""Z2 (R-25): decision logic for a supplyable zero-test salvo, without a kickback.

For each salvo S = [A1, A2, B] of results/z1_salvo.json (A1, A2 on one SW lane, 30 m apart):
a detector D (SE) is placed so that, when the test gliders pass the register (k >= 1), one of
them (the "killer") ANNIHILATES D (clean two-glider annihilation, from results/z0_pairs.json);
when the block is at 0 the test gliders are destroyed by the block and D flies on (= output Z).
In case NZ the two surviving test gliders fly on SW; one of them is the output NZ, the other is
absorbed by an eater 1 placed beyond the detector lane (searched in all orientations).

No glider of the logic ever flies back towards where the inputs come from (unlike the kickback
of R-22, whose output returns 2 lanes beside the detector's lane, see z0_rfpass.py).

Checked with the set simulator (frame of SlidingBlock.lean):
   k = 0:            counter 0 + S + D + eater  ->  counter 0 + eater + D
   k = 1..KMAX, 40:  counter k + S + D + eater  ->  counter k + eater + NZ
Usage: z2_detector.py [SALVOS.json] > results/z2_detector.txt     (writes results/z2_detector.json)
"""
import json
import os
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, counter, glider_at, transform, translate, bbox, EATER1, life   # noqa: E402
from reactions import run_free, shift_wl                                                 # noqa: E402
from net import glider_path, set_dist                                                     # noqa: E402

KMAX = 12
LD = range(-44, -9)            # detector lanes (SE lane x - y), register on -4


def annihilations():
    """(l, t): SE (0, 0) + SW (l, t) -> nothing."""
    P = json.load(open(os.path.join(HERE, 'results', 'z0_pairs.json')))
    return [(l, t) for (d2, l, t, o) in P if d2 == 'SW' and not o]


def detector_for(killer, l, t, L):
    """D = (SE, L, .) such that D, killer are the pair SE (0, 0), SW (l, t) translated."""
    # translation (p, q), delay s: SW lane l + p + q = killer lane; SE lane p - q = L
    lk, tk = killer[1], killer[2]
    if (lk - l + L) % 2:
        return None
    p = (lk - l + L) // 2
    q = lk - l - p
    s = tk - t - 4 * p
    D = shift_wl((SE, 0, 0), p, q, s)
    assert D[1] == L and shift_wl((SW, l, t), p, q, s) == killer
    return D


def run(wls, extra, t0, n):
    c = set(extra)
    for w in wls:
        c |= glider_at(*w, t0)
    return life.evolve_cells(c, n)


def outcome(S, D, k):
    t0 = min(w[2] for w in S) - 160
    st, t, rest, gl = run_free(S + [D], extra=counter(k), t0=t0, max_gen=1500, max_pop=200, max_span=200)
    if st != 'settled' or rest != counter(k):
        return None
    return sorted(gl)


def eaters_for(g, others, D, lo=8, hi=40):
    """Eaters 1 that absorb the SW glider g somewhere beyond the detector's lane, leaving the
    gliders `others` and D (in case Z) untouched (checked with the whole case later)."""
    out = []
    for j in range(lo, hi):
        for k in range(8):
            e0 = transform(EATER1, k)
            b = bbox(e0)
            for dx in range(-6, 7):
                # a point on g's lane (SW: lane = x + y) beyond the detector: x = -j - 10
                x = -j - 10 + dx
                y = g[1] - (-j - 10)
                e = frozenset(translate(e0, x - b[0], y - b[1] + 4))
                t0 = g[2] + 4 * (j + 10) - 120
                c = glider_at(*g, t0)
                if set_dist(c, e) < 3:
                    continue
                if life.evolve_cells(set(c) | e, 260) != set(e):
                    continue
                if any(set_dist(glider_path(o, t0 - 400, t0 + 1200), e) < 3 for o in others + [D]):
                    continue
                out.append(e)
        if len(out) >= 6:
            break
    return out


def job(arg):
    S, ki, (l, t) = arg
    res = []
    killer = S[ki]
    for L in LD:
        D = detector_for(killer, l, t, L)
        if D is None:
            continue
        if outcome(S, D, 0) != [D]:
            continue
        surv = sorted(w for i, w in enumerate(S) if i != ki)
        if not all(outcome(S, D, k) == surv for k in list(range(1, KMAX + 1)) + [40]):
            continue
        res.append({'S': S, 'killer': ki, 'D': D, 'surv': surv})
    return res


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'results', 'z1_salvo.json')
    salvos = json.load(open(src))
    salvos = [[tuple(tuple(x) if isinstance(x, list) else x for x in w) for w in S] for S in salvos]
    ann = annihilations()
    print('salvos %d, annihilating pairs SE + SW: %d' % (len(salvos), len(ann)))
    good = []
    with Pool(8) as p:
        for res in p.imap_unordered(job, [(S, ki, a) for S in salvos for ki in range(3) for a in ann], chunksize=4):
            for r in res:
                print('  salvo %s killer %d D %s survivors %s' % (r['S'], r['killer'], r['D'], r['surv']), flush=True)
            good += res
    print('designs (Z and NZ correct without eaters): %d' % len(good))
    json.dump(good, open(os.path.join(HERE, 'results', 'z2_detector.json'), 'w'))


if __name__ == '__main__':
    main()
