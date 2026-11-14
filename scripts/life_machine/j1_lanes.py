#!/usr/bin/env python3
"""J1 (R-24): which pull salvo and which push salvo can share ONE block and ONE diagonal of final
insertion reflectors?  Cheap combinatorics before any timing equations.

Input: scripts/life_search/results/block_salvo_hits.txt (read-only): every two- and three-glider
salvo from the NW that moves a block by (-1, -1) (pulls, 513) or (+1, +1) (pushes, 176), each
re-checked here by simulation, plus their mirror images in the diagonal (sym 6: x <-> y; the block
at (0, 0) is invariant, lanes change sign).  Frame: the block has its upper left cell at (0, 0);
a salvo is a list of SE world lines (lane, tau), tau relative to the last glider (as p1_pushes).

The model of the final insertion stage (net.insertion_clear, R-22 section 2): every salvo glider is
put onto its lane by a reflector beside the diagonal; a glider already in flight passes a
reflector only on its far side, 4 or more lanes away (statically, i.e. for a foreign salvo, this
is the only condition; for the own salvo also the timing window applies).  All final reflectors
of both generators stand on one diagonal in some order, so (see R-24 section 2) the union of the
lanes of the two salvos must have all gaps >= 4 and there must be ONE outward order of insertion
(each new lane a new extreme of the lanes already present: below the minimum by >= 4 for an
R-type reflector (input SW), above the maximum by >= 4 for an L-type one (input NE)) whose
restriction to each salvo satisfies the timing rule of insertion_clear.

Also: (2) the same with SHARED gliders (pull and push gliders on one lane leave one reflector whose
input comes from an OR gate: a copy of blockedStream released by either of two control gliders; the
two gliders must then have the same tau offset mod 30), (3) one existing generator kept (PG1 of
R-21, PSG1 of R-23) and the other salvo sharing one of its gliders.

Output: results/j1_lanes.txt (stdout), results/j1_lanes.json (the pairs of (2)).
"""
import itertools
import json
import os
import re
import sys

from common import HERE, life, evolve_cells, translate, transform, glider_at, SE
from net import insertion_clear

HITS = os.path.join(HERE, '..', 'life_search', 'results', 'block_salvo_hits.txt')
BLOCK0 = frozenset({(0, 0), (1, 0), (0, 1), (1, 1)})


def load(disp):
    out = []
    for line in open(HITS):
        if line.startswith('#'):
            continue
        head, names, nf = [s.strip() for s in line.split('|')]
        h = head.split()
        if (int(h[0]), int(h[1])) != disp:
            continue
        n = int(h[2])
        gl = []
        for tok in nf.split():
            m = re.fullmatch(r'(-?\d+),(-?\d+)\+(\d+)', tok)
            x, y, t = int(m.group(1)), int(m.group(2)), int(m.group(3))
            gl.append(evolve_cells(translate(life.GLIDER, x, y), t))
        cells = set().union(*gl)
        assert len(cells) == 5 * len(gl)
        for sym in (0, 6):
            c = set(transform(cells, sym)) if sym else set(cells)
            wls = []
            for g in gl:
                w = life.glider_worldline(set(transform(g, sym)) if sym else g, 0)
                assert w is not None and w[0] == SE
                wls.append(w)
            end = evolve_cells(c | BLOCK0, n)
            assert end == translate(BLOCK0, *disp), line
            t0 = max(w[2] for w in wls)
            wl = tuple(sorted([(w[1], w[2] - t0) for w in wls], key=lambda w: (w[1], w[0])))
            out.append({'wl': wl, 'n': n, 'name': names, 'mirror': sym == 6})
    # deduplicate (a salvo may occur twice when it is its own mirror image up to ordering)
    seen, res = set(), []
    for r in out:
        if r['wl'] in seen:
            continue
        seen.add(r['wl'])
        res.append(r)
    return res


def outward_orders(A, B):
    """Outward insertion orders of the union of the gliders A (salvo 1) and B (salvo 2), given as
    lists of (lane, tau); yields lists of (salvo index, glider, type)."""
    allg = [(0, g) for g in A] + [(1, g) for g in B]
    lanes = sorted(g[1][0] for g in allg)
    if any(b - a < 4 for a, b in zip(lanes, lanes[1:])):
        return
    allg.sort(key=lambda g: g[1][0])
    n = len(allg)
    for start in range(n):
        # choose the sequence of extensions: left/right
        for pattern in itertools.product((0, 1), repeat=n - 1):
            lo = hi = start
            seq = [allg[start]]
            ok = True
            for p in pattern:
                if p == 0:
                    if lo == 0:
                        ok = False
                        break
                    lo -= 1
                    seq.append(allg[lo])
                else:
                    if hi == n - 1:
                        ok = False
                        break
                    hi += 1
                    seq.append(allg[hi])
            if not ok:
                continue
            present = ([], [])
            res = []
            for (s, g) in seq:
                ty = insertion_clear(g, present[s])
                if ty is None:
                    break
                # side relative to all gliders present (foreign ones too)
                every = present[0] + present[1]
                if every:
                    ty = 'L' if all(o[0] <= g[0] - 4 for o in every) else 'R'
                res.append((s, g, ty))
                present[s].append(g)
            else:
                yield res


def win(ty, d, dt):
    """The forbidden window of net.insertion_clear for a reflector of type ty inserting a glider
    while an own glider d lanes away (far side) flies past with delay dt."""
    hi = 21 if d < 6 else 23
    if ty == 'L':
        return -13 <= dt <= hi
    return -13 - 4 * d <= dt <= hi - 4 * d


def shared_orders(A, B):
    """Outward insertion orders when gliders of A and B on the same lane share one reflector (its
    input fed by an OR gate); the shared gliders must have the same tau mod 30 offset (a reflector
    and a gate are period 30).  Returns the list of lane orders."""
    la = [g[0] for g in A]
    lb = [g[0] for g in B]
    if len(set(la)) < len(la) or len(set(lb)) < len(lb):
        return []
    pa, pb = dict(A), dict(B)
    sh = set(pa) & set(pb)
    if len(set((pa[l] - pb[l]) % 30 for l in sh)) > 1:
        return []
    lanes = sorted(set(la) | set(lb))
    if any(y - x < 4 for x, y in zip(lanes, lanes[1:])):
        return []
    n = len(lanes)
    res = []
    for start in range(n):
        for pat in itertools.product((0, 1), repeat=n - 1):
            lo = hi = start
            seq = [lanes[start]]
            ok = True
            for p in pat:
                if p == 0:
                    if lo == 0:
                        ok = False
                        break
                    lo -= 1
                    seq.append(lanes[lo])
                else:
                    if hi == n - 1:
                        ok = False
                        break
                    hi += 1
                    seq.append(lanes[hi])
            if not ok:
                continue
            good = True
            for S in (A, B):
                pres = []
                for l in seq:
                    for g in S:
                        if g[0] == l:
                            if insertion_clear(g, pres) is None:
                                good = False
                            pres.append(g)
            if good:
                res.append(seq)
    return res


def fixed_generator(fixed, family):
    """One generator kept as it is (fixed = [(name, lane, type, tau)] in insertion order); the other
    salvo must share at least one of its gliders (OR gate) and insert its own gliders with reflectors
    of free type at free positions of the order.  Returns [(salvo, order, types)]."""
    out = []
    fl = {f[1]: f for f in fixed}
    for Q in family:
        q = list(Q['wl'])
        if len(set(g[0] for g in q)) < len(q):
            continue
        shared = [g for g in q if g[0] in fl]
        if not shared:
            continue
        if len(set((g[1] - fl[g[0]][3]) % 30 for g in shared)) > 1:
            continue
        refl = [[f[0], f[1], (f[2],), [('F', (f[1], f[3]))]] for f in fixed]
        for g in shared:
            for r in refl:
                if r[1] == g[0]:
                    r[3].append(('Q', g))
        nf = len(refl)
        for g in q:
            if g[0] not in fl:
                refl.append(['q%d' % g[0], g[0], ('L', 'R'), [('Q', g)]])
        for perm in itertools.permutations(range(len(refl))):
            if [i for i in perm if i < nf] != list(range(nf)):
                continue
            for tys in itertools.product(*[refl[i][2] for i in perm]):
                ok = True
                for xi in range(len(perm)):
                    X = refl[perm[xi]]
                    tx = tys[xi]
                    for yi in range(xi):
                        Y = refl[perm[yi]]
                        if tx == 'L' and not Y[1] <= X[1] - 4:
                            ok = False
                        if tx == 'R' and not Y[1] >= X[1] + 4:
                            ok = False
                        for (s1, g1) in X[3]:
                            for (s2, g2) in Y[3]:
                                if s1 == s2 and win(tx, abs(X[1] - Y[1]), g2[1] - g1[1]):
                                    ok = False
                    if not ok:
                        break
                if ok:
                    out.append((q, [refl[i][0] for i in perm], tys))
    return out


def main():
    pulls = load((-1, -1))
    pushes = load((1, 1))
    print('pulls (2 or 3 gliders, with mirror images, re-checked): %d; pushes: %d' % (len(pulls), len(pushes)))
    pairs = []
    for P in pulls:
        for Q in pushes:
            orders = list(outward_orders(P['wl'], Q['wl']))
            if orders:
                pairs.append({'pull': P, 'push': Q, 'orders': orders})
    print('(1) without shared gliders: compatible (pull, push) pairs (union of lanes with gaps >= 4, one '
          'outward order with the timing rule for each salvo): %d' % len(pairs))
    P2, Q2 = load((-2, -2)), load((2, 2))
    n2 = sum(1 for P in P2 for Q in Q2 if any(True for _ in outward_orders(P['wl'], Q['wl'])))
    print('    the same for salvos moving the block by (-2, -2) / (+2, +2) (%d / %d): %d' % (len(P2), len(Q2), n2))
    print('(2) with shared gliders (one reflector, its input fed by an OR gate; same tau mod 30 offset):')
    sh = []
    for P in pulls:
        for Q in pushes:
            o = shared_orders(P['wl'], Q['wl'])
            if o:
                sh.append((P, Q, o))
                pl, ql = dict(P['wl']), dict(Q['wl'])
                print('    pull %s  push %s  shared lanes %s  orders %s' % (list(P['wl']), list(Q['wl']), sorted(set(pl) & set(ql)), o))
    print('    pairs: %d' % len(sh))
    print('(3) PG1 kept (a: lane -1 type R first, b: lane 5 type L), pushes sharing a glider of it:')
    for r in fixed_generator([('a', -1, 'R', 0), ('b', 5, 'L', -29)], pushes):
        print('    push %s  order %s  types %s' % r)
    r = fixed_generator([('c', 5, 'R', -42), ('a', 0, 'R', 0), ('b', 12, 'L', -27)], pulls)
    print('    PSG1 kept (c, a, b of R-23), pulls sharing a glider of it: %d' % len(r))
    json.dump([{'pull': [list(w) for w in P['wl']], 'push': [list(w) for w in Q['wl']], 'orders': o} for (P, Q, o) in sh],
              open(os.path.join(HERE, 'results', 'j1_lanes.json'), 'w'))


if __name__ == '__main__':
    main()
