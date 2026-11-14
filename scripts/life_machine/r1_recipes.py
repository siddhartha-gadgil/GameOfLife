#!/usr/bin/env python3
"""Search R1: slow free-glider recipes with one lane per direction.

Why: two gliders of a salvo cannot both be direct outputs of gates (their lanes are 6 apart or
equal, and a gun blocks all parallel lanes within about 22 of its stream, see r0_obstruction.py).
The other gliders must be made by collisions in front of the guns, from gliders that gates can
supply: per direction ONE lane (one gun), gliders on it a multiple of 30 generations apart.

Tree search.  Root: every interacting pair of gliders of two different directions among
SE, SW, NE (up to translation in space and time).  Child: one more glider is added after the
configuration has settled into a still life or period-2 oscillator R (plus departed gliders):
  * from a direction used before: on the same lane, 30 n generations after the previous one
    (n minimal such that it arrives after R has settled);
  * from a new direction: on every lane that comes within distance 2 of the box of R, both
    parities of tau if R has period 2.
A node with R empty and at least one departed glider is a *recipe*.  Depth: MAXG gliders.

Usage: r1_recipes.py [MAXG] [sides]   (default 4; `sides`: only SW and NE gliders, i.e. a pure
       insertion from the two sides)       Output: results/r1_recipes_<MAXG>[_sides].json.gz
"""
import gzip
import json
import os
import sys
import time
from multiprocessing import Pool

from common import glider_at, bbox, SE, SW, NE, NW, DIRNAME
import recipes
from recipes import settle, place, glider_box, _cheb_box

DIRS3 = [SE, SW, NE]
MAXG = 4


def start_pair(w1, w2):
    """Time t0 at which the two gliders are still >= 6 apart (and were before); None if they never
    come within 6."""
    prev_far = None
    for t in range(-600, 600):
        b1 = bbox(glider_at(*w1, t))
        b2 = bbox(glider_at(*w2, t))
        if _cheb_box(b1, b2) < 6:
            return prev_far
        prev_far = t
    return None


def roots():
    out = []
    # SE (lane 0, tau 0) with SW (lane w in {0, 1}, tau = 4 w + i)
    for w in (0, 1):
        for i in range(-48, 49):
            out.append(((SE, 0, 0), (SW, w, 4 * w + i)))
    # SE (lane 0, tau 0) with NE (lane n in {0, 1}, tau = i)
    for n in (0, 1):
        for i in range(-48, 49):
            out.append(((SE, 0, 0), (NE, n, i)))
    # SW (lane 0, tau 0) with NE (lane offset c, tau mod 8)
    for c in range(-14, 15):
        for i in range(8):
            out.append(((SW, 0, 0), (NE, c, i)))
    return out


def expand(node, found, seen, stats):
    """node = (rest, t, lanes, inputs, outputs); lanes: {d: (lane, tau of the last glider)}."""
    rest, t, lanes, inputs, outputs = node
    if not rest:
        if outputs:
            found.append({'in': inputs, 'out': outputs})
        return
    if len(inputs) >= MAXG:
        return
    p2 = (recipes.step_cells(set(rest)) != set(rest))
    b = bbox(rest)
    box = (b[0] - 1, b[1] - 1, b[2] + 1, b[3] + 1) if p2 else b
    cands = []
    for d in DIRS3:
        if d in lanes:
            lane, tau_prev = lanes[d]
            wl = place(box, d, lane, t, tau_prev % 30, 30)
            if wl is not None:
                cands.append(wl)
        else:
            vals = [d[1] * x - d[0] * y for x in (box[0], box[2]) for y in (box[1], box[3])]
            for lane in range(min(vals) - 6, max(vals) + 4):
                for par in ((0, 1) if p2 else (0,)):
                    wl = place(box, d, lane, t, par, 2)
                    if wl is not None:
                        cands.append(wl)
    for wl in cands:
        cells = set(rest) | glider_at(*wl, t)
        st, t2, rest2, gl = settle(cells, t)
        stats['runs'] = stats.get('runs', 0) + 1
        if st != 'settled':
            stats['fail'] = stats.get('fail', 0) + 1
            continue
        if rest2 == rest and gl == [wl]:
            continue                                  # no interaction
        lanes2 = dict(lanes)
        lanes2[wl[0]] = (wl[1], wl[2])
        outs2 = outputs + gl
        key = (rest2, t2 % 2 if rest2 else 0,
               tuple(sorted((d, v[0], v[1] % 2) for d, v in lanes2.items())),
               tuple(sorted((g[0], g[1]) for g in outs2)))
        if key in seen:
            continue
        seen.add(key)
        expand((rest2, t2, lanes2, inputs + [wl], outs2), found, seen, stats)


def work(pair):
    w1, w2 = pair
    found, stats = [], {}
    t0 = start_pair(w1, w2)
    if t0 is None:
        return found, stats, 0
    cells = glider_at(*w1, t0) | glider_at(*w2, t0)
    st, t, rest, gl = settle(cells, t0)
    if st != 'settled':
        return found, {'root-fail': 1}, 1
    if not rest and sorted(gl) == sorted([w1, w2]):
        return found, stats, 0
    lanes = {w1[0]: (w1[1], w1[2]), w2[0]: (w2[1], w2[2])}
    expand((rest, t, lanes, [w1, w2], gl), found, set(), stats)
    return found, stats, 1


def init(maxg, dirs):
    global MAXG, DIRS3
    MAXG = maxg
    DIRS3 = dirs


def main():
    global MAXG, DIRS3
    tag = ''
    if len(sys.argv) > 1:
        MAXG = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] == 'sides':      # gliders from the two sides only
        DIRS3 = [SW, NE]
        tag = '_sides'
    t = time.time()
    found, stats, nroot = [], {}, 0
    rts = [p for p in roots() if p[0][0] in DIRS3 and p[1][0] in DIRS3]
    with Pool(min(20, os.cpu_count() or 1), initializer=init, initargs=(MAXG, DIRS3)) as pool:
        for f, s, r in pool.imap_unordered(work, rts, chunksize=2):
            found.extend(f)
            nroot += r
            for k, v in s.items():
                stats[k] = stats.get(k, 0) + v
    dt = time.time() - t
    os.makedirs('results', exist_ok=True)
    with gzip.open('results/r1_recipes_%d%s.json.gz' % (MAXG, tag), 'wt') as f:
        json.dump({'maxg': MAXG, 'roots': nroot, 'stats': stats, 'seconds': round(dt, 1),
                   'recipes': found}, f, separators=(',', ':'))
    print('interacting roots %d, stats %s, recipes (empty rest, >= 1 glider out): %d, %.1f s'
          % (nroot, stats, len(found), dt))
    summary(found)


def usable(r):
    """Output directions d such that no input glider has direction -d."""
    ins = {tuple(w[0]) for w in r['in']}
    return [tuple(o[0]) for o in r['out'] if (-o[0][0], -o[0][1]) not in ins]


def summary(found):
    cnt = {}
    for r in found:
        key = (len(r['in']), ''.join(sorted(DIRNAME[tuple(w[0])][0:2] + ' ' for w in r['in'])).strip(),
               ' '.join(sorted(DIRNAME[tuple(o[0])] for o in r['out'])))
        cnt[key] = cnt.get(key, 0) + 1
    print('recipes by (number of input gliders, input directions, output directions):')
    for key in sorted(cnt):
        print('   ', key, cnt[key])
    print('recipes with exactly one output glider, whose direction is not opposite to any input:')
    for r in found:
        if len(r['out']) == 1 and usable(r) and len(r['in']) >= 3:
            print('   in', [(DIRNAME[tuple(w[0])], w[1], w[2]) for w in r['in']],
                  'out', [(DIRNAME[tuple(o[0])], o[1], o[2]) for o in r['out']])


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    if len(sys.argv) == 3 and sys.argv[1] == 'summary':
        summary(json.load(gzip.open(sys.argv[2], 'rt'))['recipes'])
    else:
        main()
