#!/usr/bin/env python3
"""Segment plan for a network certificate (untrusted oracle; Lean is the check).

A run of a circuit of periodic pieces (period 30) and still-life groups (register blocks) is cut
into segments [a, b).  In a segment every group is either
  * idle: its cells are its own cycle (pieces) or an unchanged still life; footprint = its
    envelope box;
  * active: a local certificate of its window (all live cells within its envelope + ME, plus the
    gliders that belong to the reaction); footprint = the tight box of the isolated evolution;
and every other live cell belongs to a free object (a glider or a salvo) in flight, with a moving
box footprint (the box of its first four generations, moved by the direction every four
generations).  All footprints of a segment are checked pairwise far apart (gap >= 3 between
boxes, as `Box.farApart` with r = 2 needs), with the same box formulas as the Lean side, and the
isolated evolutions are checked to add up to the true evolution.
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_gates'))
from life import step_cells, bbox, components, translate  # noqa: E402

ME = 6          # detection margin around an envelope
CHUNK = 200     # maximal length of one local certificate
GAP = 3         # boxes far apart: b + 2 < a'  <=>  a' - b >= 3


def far(b1, b2):
    """Boxes (x0, y0, x1, y1) far apart in the sense of `Box.farApart` with r = 2."""
    return (b1[2] + 2 < b2[0] or b2[2] + 2 < b1[0] or b1[3] + 2 < b2[1] or b2[3] + 2 < b1[1])


def grow(b, m):
    return (b[0] - m, b[1] - m, b[2] + m, b[3] + m)


def inside(c, b):
    return b[0] <= c[0] <= b[2] and b[1] <= c[1] <= b[3]


def restrict(cells, b):
    return {c for c in cells if inside(c, b)}


def union_box(a, b):
    if a is None:
        return b
    return (min(a[0], b[0]), min(a[1], b[1]), max(a[2], b[2]), max(a[3], b[3]))


def evolve(cells, n):
    for _ in range(n):
        cells = step_cells(cells)
    return cells


def motion(cells):
    """(v, phase box) if the cells move by v in(+-1, +-1) every 4 generations, else None."""
    c4 = evolve(set(cells), 4)
    if not c4 or not cells:
        return None
    b0, b4 = bbox(cells), bbox(c4)
    v = (b4[0] - b0[0], b4[1] - b0[1])
    if abs(v[0]) != 1 or abs(v[1]) != 1 or translate(cells, *v) != c4:
        return None
    pb = None
    c = set(cells)
    for _ in range(4):
        pb = union_box(pb, bbox(c))
        c = step_cells(c)
    return v, pb


def moving_box(pb, v, q):
    return (pb[0] + v[0] * q, pb[1] + v[1] * q, pb[2] + v[0] * q, pb[3] + v[1] * q)


class Group:
    def __init__(self, name, kind, env, rest=None):
        self.name, self.kind, self.env, self.rest = name, kind, env, rest   # rest(t) for pieces
        self.ext = grow(env, ME)


def detect(groups, start, Ts, N, cycle_all, log=None):
    """Pass 1: activity intervals [s, e] per group: times when the cells within env + ME differ
    from the rest (the pieces' cycle; for a still group, from the cells one generation before or
    after).  cycle_all(t) = the cells of all pieces at rest at time t."""
    act = {g.name: [] for g in groups}
    c = set(start)
    prevd = None
    for i in range(N + 1):
        t = Ts + i
        diff = c ^ cycle_all(t)
        on = set()
        for q in diff:
            for g in groups:
                if g.kind == 'piece' and inside(q, g.ext):
                    on.add(g.name)
        for g in groups:
            if g.kind == 'still':
                loc = restrict(diff, g.ext)
                if prevd is not None and loc != restrict(prevd, g.ext):
                    on.add(g.name)
                    # the previous generation too
                    iv = act[g.name]
                    if not (iv and iv[-1][1] >= t - 1):
                        iv.append([t - 1, t - 1])
        for name in on:
            iv = act[name]
            if iv and iv[-1][1] >= t - 8:
                iv[-1][1] = t
            else:
                iv.append([t, t])
        prevd = diff
        if i < N:
            c = step_cells(c)
        if log and i % 2000 == 0:
            log('detect %d/%d' % (i, N))
    return act


def partition(groups, cells, t, activeset):
    """Split the live cells at time t: idle groups take exactly their rest cells; every remaining
    connected component (Chebyshev distance <= 2) goes to the active or still group whose env + ME
    it meets, or else is a free object."""
    own = {g.name: set() for g in groups}
    rest = set(cells)
    for g in groups:
        if g.kind == 'piece' and g.name not in activeset:
            loc = set(g.rest(t))
            if not loc <= rest:
                raise ValueError(('idle piece not at rest', g.name, t))
            own[g.name] = loc
            rest -= loc
    free = []
    for comp in components(rest, 2):
        comp = set(comp)
        hit = [g for g in groups if (g.kind == 'still' or g.name in activeset)
               and any(inside(q, g.ext) for q in comp)]
        if len(hit) > 1:
            raise ValueError(('component meets two groups', t, [g.name for g in hit]))
        if hit:
            own[hit[0].name] |= comp
        else:
            free.append(comp)
    return own, free


def segment(groups, cells, a, b, activeset, merges=()):
    """Build and check the processes of the segment [a, b) from the cells at time a.  Returns
    (procs, cells at b) or raises ValueError(time of the problem)."""
    own, free = partition(groups, cells, a, activeset)
    procs = []
    for g in groups:
        if g.name in activeset:
            procs.append({'kind': 'cert', 'group': g.name, 'start': own[g.name], 'box': None})
        elif g.kind == 'piece':
            procs.append({'kind': 'idle', 'group': g.name, 'start': own[g.name], 'box': g.env})
        else:
            if not own[g.name]:
                continue
            procs.append({'kind': 'still', 'group': g.name, 'start': own[g.name],
                          'box': bbox(own[g.name])})
    merged = [set() for _ in merges]
    rest_free = []
    for f in free:
        hit = [k for k, (gname, ms) in enumerate(merges) if f & ms]
        if hit:
            merged[hit[0]] |= f
        else:
            rest_free.append(f)
    for (gname, ms), mc in zip(merges, merged):
        if not mc:
            continue
        tgt = [p for p in procs if p['kind'] == 'cert' and p['group'] == gname] if gname else []
        if tgt:
            tgt[0]['start'] = set(tgt[0]['start']) | mc
        else:
            procs.append({'kind': 'cert', 'group': None, 'start': mc, 'box': None})
    for f in rest_free:
        m = motion(f)
        if m is None:
            raise ValueError(('free object does not fly', a, sorted(f)[:8]))
        procs.append({'kind': 'flight', 'start': f, 'v': m[0], 'pb': m[1]})
    n = b - a
    # isolated evolutions: the certificates' footprints are one box for the whole segment
    cur = [set(p['start']) for p in procs]
    for p in procs:
        if p['kind'] == 'cert':
            p['box'] = bbox(p['start']) if p['start'] else None
    for i in range(n):
        cur = [step_cells(c) if p['kind'] in ('cert', 'flight') else c for p, c in zip(procs, cur)]
        for p, c in zip(procs, cur):
            if p['kind'] == 'cert' and c:
                p['box'] = union_box(p['box'], bbox(c))
    for p, c in zip(procs, cur):
        p['stop'] = c
    static = [x for x, p in enumerate(procs) if p['kind'] != 'flight']
    for x in static:
        for y in static:
            if y < x and procs[x]['box'] is not None and procs[y]['box'] is not None \
                    and not far(procs[x]['box'], procs[y]['box']):
                raise ValueError(('near', a, procs[x].get('group'), procs[y].get('group'),
                                  procs[x]['box'], procs[y]['box'], 'segment', a, b, sorted(activeset)))
    for i in range(0, n, 4):
        boxes = [moving_box(p['pb'], p['v'], i // 4) if p['kind'] == 'flight' else p['box']
                 for p in procs]
        for x, p in enumerate(procs):
            if p['kind'] != 'flight':
                continue
            for y in range(len(procs)):
                if y == x or boxes[y] is None or (procs[y]['kind'] == 'flight' and y > x):
                    continue
                if not far(boxes[x], boxes[y]):
                    raise ValueError(('near', a + i, 'flight', procs[y].get('group', 'flight')
                                      if procs[y]['kind'] != 'flight' else 'flight',
                                      boxes[x], boxes[y], 'segment', a, b, sorted(activeset)))
    for p in procs:
        if p['kind'] == 'idle':
            g = [g for g in groups if g.name == p['group']][0]
            p['stop'] = set(g.rest(b))
    total = set()
    for p in procs:
        total |= p['stop']
    return procs, total


def plan(groups, start, Ts, N, cycle_all, log=None, extra_bounds=()):
    act = detect(groups, start, Ts, N, cycle_all, log)
    if log:
        log('activity: %s' % {k: v for k, v in act.items() if v})
    bounds = {Ts, Ts + N}
    for name, ivs in act.items():
        for s, e in ivs:
            bounds.add(max(Ts, s))
            bounds.add(min(Ts + N, e + 1))
    bounds |= {t for t in extra_bounds if Ts < t < Ts + N}
    bounds = sorted(bounds)
    # long active segments are cut into certificates of at most CHUNK generations
    extra = set()
    for a, b in zip(bounds, bounds[1:]):
        if any(any(s <= a and b <= e + 1 for s, e in ivs) for ivs in act.values()):
            extra |= set(range(a + CHUNK, b, CHUNK))
    bounds = sorted(set(bounds) | extra)
    segs = []
    c = set(start)
    bi = 0
    merges = {}
    while bi < len(bounds) - 1:
        a, b = bounds[bi], bounds[bi + 1]
        activeset = {name for name, ivs in act.items()
                     if any(s <= a and b <= e + 1 for s, e in ivs)}
        try:
            procs, total = segment(groups, c, a, b, activeset, merges.get(a, ()))
        except ValueError as err:
            info = err.args[0]
            if info[0] == 'near' and info[2] == info[3] == 'flight' and info[1] - 3 <= a:
                # two free objects meet: a local certificate of the pair from a, until they are
                # gone or fly apart
                own, free = partition(groups, c, a, activeset)
                bx = [info[4], info[5]]
                pair = set()
                for f in free:
                    fb = bbox(evolve(set(f), info[1] - a))
                    if any(not far(grow(fb, 4), q) for q in bx):
                        pair |= f
                cur, t = set(pair), a
                while cur and t < b:
                    cur = step_cells(cur)
                    t += 1
                    comps = [set(x) for x in components(cur, 2)]
                    if cur and all(motion(x) for x in comps) and all(
                            far(grow(bbox(x), 6), bbox(y)) for x in comps for y in comps if x is not y):
                        break
                merges.setdefault(a, []).append((None, pair))
                if t < b and t not in bounds:
                    bounds.insert(bi + 1, t)
                if log:
                    log('free collision at %d..%d (%d cells)' % (a, t, len(pair)))
                continue
            if info[0] == 'near' and info[2] == 'flight' and info[3] not in ('flight', None) \
                    and info[3] in activeset and info[1] - 3 <= a:
                # an object comes near an active certificate: the certificate takes it
                own, free = partition(groups, c, a, activeset)
                for f in free:
                    fb = bbox(evolve(set(f), info[1] - a))
                    if not far(grow(fb, 2), info[5]):
                        merges.setdefault(a, []).append((info[3], f))
                if log:
                    log('absorb at %d into %s' % (a, info[3]))
                continue
            if info[0] == 'near' and 'flight' in (info[2], info[3]) and info[1] - 3 > a:
                # an object comes near a process: cut the segment shortly before
                t = info[1] - 3
                bounds.insert(bi + 1, t)
                if log:
                    log('cut at %d (%s)' % (t, info[2:4]))
                continue
            raise
        c_true = evolve(c, b - a)
        if total != c_true:
            raise ValueError(('isolated evolutions differ from the truth', a, b,
                              len(total ^ c_true)))
        segs.append({'a': a, 'b': b, 'procs': procs})
        c = c_true
        bi += 1
        if log:
            log('segment %d..%d: %d procs, active %s' % (a, b, len(procs), sorted(activeset)))
    return act, segs, c
