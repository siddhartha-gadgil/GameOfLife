#!/usr/bin/env python3
"""F3: comb fan-out.  One control glider in, n + 1 gliders out, n + 1 assemblies (2 n + 2 guns).

The round trip of f2_roundtrip.py, repeated: in a verified fan-out (S, K1) the glider G1 released
by K1 is, in the own coordinates of K1, a glider of its stream A, (SE, 14, 29 mod 30) -- exactly
what G0 is for S (this holds for K1 a translate of `blockedStream` or its image under sym_7; not
for the images under sym_4, whose G1 is a glider of stream B).  So a further assembly K2, placed
relative to K1 as the second assembly of ANY verified fan-out is placed relative to S, kicks G1
back into K1, which releases a glider of its stream B, and K2 releases a glider of its own.

  comb (f1, f2):  S, K1 = f1, K2 = K1 o f2    outputs  G2 (stream B of S), G2' (stream B of K1),
                                                       G1' (stream of K2)
All pairs (f1, f2) of the 77 fan-outs with f1 of type 0 or 7 are simulated (control glider
C0 = (SE, 41, 22); board, then the set simulator on the unbounded plane); the reuse spacing T
(the smallest multiple of 30 for which a second control glider works) is computed for the 12
smallest combs only (function `reuse`).

Usage: f3_comb.py        Output: results/f3_comb.json.gz, summary on stdout
"""
import gzip
import json
import os
import time
from multiprocessing import Pool

from common import SE, SW, NW, NE, DIRNAME, bbox
import net
from net import compose, wl_in, wl_out, env_box, box_dist

C0 = (SE, 41, 22)
S = ('asm', 0, 0, 0, 0)
G0 = (SE, 14, 119)


def tup(o):
    return (tuple(o[0]), o[1], o[2])


def outs_of(f):
    outs = [tup(o) for o in f['outs']]
    g2 = [w for w in outs if w[0] == SW and w[1] == 75][0]
    g1 = [w for w in outs if w != g2][0]
    return g1, g2


def predict(f1, f2):
    """Pieces and predicted outputs of the comb (f1, f2)."""
    K1 = ('asm',) + tuple(f1['asm'])
    g1, g2 = outs_of(f1)
    own = wl_in(g1, K1)
    assert own[:2] == G0[:2] and (own[2] - G0[2]) % 30 == 0
    dt = own[2] - G0[2]
    K2 = compose(K1, ('asm',) + tuple(f2['asm']))
    h1, h2 = outs_of(f2)
    o1 = wl_out((h1[0], h1[1], h1[2] + dt), K1)       # stream glider of K2
    o2 = wl_out((h2[0], h2[1], h2[2] + dt), K1)       # stream B glider of K1
    return [S, K1, K2], [g2, o2, o1]


def simulate(job):
    i, j, f1, f2 = job
    pieces, want = predict(f1, f2)
    boxes = [env_box(p) for p in pieces]
    sep = min(box_dist(boxes[a], boxes[b]) for a in range(3) for b in range(a))
    rec = {'i': i, 'j': j, 'pieces': pieces, 'outs': want, 'sep': sep}
    if sep < 6:
        return rec, 'too close'
    try:
        nt = net.Net(pieces, ['S', 'K1', 'K2'])
    except (ValueError, AssertionError):
        return rec, 'not periodic'
    st, outs, Ts, Te = nt.react([C0], limit=6000)
    if st != 'ok':
        return rec, st
    if outs != sorted(want):
        return rec, 'other gliders'
    rec.update(Ts=Ts, Te=Te, N=Te - Ts, env=list(nt.env), T='?')
    return rec, 'ok'


def reuse(rec, mmin=8, mmax=40):
    """The smallest reuse spacing T = 30 m of a verified comb (None if none up to 30 mmax)."""
    nt = net.Net([tuple(p) for p in rec['pieces']], ['S', 'K1', 'K2'])
    want = [tup(o) for o in rec['outs']]
    for m in range(mmin, mmax):
        c2 = (C0[0], C0[1], C0[2] + 30 * m)
        st2, outs2, _, _ = nt.react([C0, c2], limit=6000)
        if st2 == 'ok' and outs2 == sorted(want + [(w[0], w[1], w[2] + 30 * m) for w in want]):
            return 30 * m
    return None


def main():
    t = time.time()
    fos = json.load(gzip.open('results/f2_roundtrip.json.gz', 'rt'))['good']
    jobs = [(i, j, f1, f2) for i, f1 in enumerate(fos) if f1['asm'][0] in (0, 7) for j, f2 in enumerate(fos)]
    good, stats = [], {}
    with Pool(min(20, os.cpu_count() or 1)) as pool:
        for rec, st in pool.imap_unordered(simulate, jobs, chunksize=4):
            stats[st] = stats.get(st, 0) + 1
            if st == 'ok':
                good.append(rec)
    good.sort(key=lambda r: ((r['env'][2] - r['env'][0]) * (r['env'][3] - r['env'][1])))
    print('combs (f1, f2) tried: %d: %s (%.0f s)' % (len(jobs), stats, time.time() - t))
    for r in good[:12]:
        r['T'] = reuse(r)
    for r in good[:30]:
        print('  f1 %d f2 %d: K1 %s K2 %s outs %s env %s N %d T %s sep %d' % (
            r['i'], r['j'], r['pieces'][1][1:], r['pieces'][2][1:],
            [(DIRNAME[w[0]], w[1], w[2]) for w in r['outs']], r['env'], r['N'], r['T'], r['sep']))
    with gzip.open('results/f3_comb.json.gz', 'wt') as f:
        json.dump({'stats': stats, 'good': good}, f, separators=(',', ':'))


if __name__ == '__main__':
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
