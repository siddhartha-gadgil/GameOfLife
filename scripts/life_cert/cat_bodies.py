#!/usr/bin/env python3
"""The 2 unit bodies of the R-31 catalogue (untrusted extractor; exact simulation).

Unit template U(kind, n) of p0_parts (local frame: last entry copy = ('asm', 0, 0, 0, 0)); the body
is fed by the chain output (SE, 14, 119) of that copy (independent of n and of the copy t).
  dec: fan-out F_B + F_A (outputs L (SW), R (NE), D (SE)), then RF0 turning L -> SE, RF0 turning
       R -> SE, and the jog of D: RF0 SE -> NE, RF0 NE -> SE;
  inc: fan-out F_A (outputs R (NE), D (SE)), then RF0 turning R -> SE.
Each stage is checked alone, each RF0 is matched to one of the 8 certified images (rf_images.py:
G = transform(RF0, k), In = transform(IN, k) at phase 0, Out 30 generations later), and the whole
body is checked as one reaction.
Usage: cat_bodies.py  -> results/cat_bodies.json"""
import json
from cat_common import *  # noqa
import p0_parts
from life import transform, glider_worldline

RF0 = cells_of_window(0, 2, [12288, 34816, 66563, 214019, 66560, 1607680, 2633728, 2097152, 6291456])
IN = cells_of_window(20, 0, [1, 5, 3])
OUT = cells_of_window(11, -4, [2, 3, 5])
DN = {(1, 1): 'SE', (-1, 1): 'SW', (1, -1): 'NE', (-1, -1): 'NW'}


def match_rf(piece, w_in, w_out):
    E = Env(env_cells(piece))
    tc, t_in, t_out = approach(E, w_in, time_at(w_in, bbox(env_cells(piece))[:2]), span=600)
    found = []
    for k in range(8):
        G, I, O = transform(RF0, k), transform(IN, k), transform(OUT, k)
        bG = bbox(G)
        for t in range(tc - 200, tc + 60):
            pc = piece_cells(piece, t)
            b = bbox(pc)
            dx, dy = b[0] - bG[0], b[1] - bG[1]
            if pc == translate(G, dx, dy) and gl(w_in, t) == translate(I, dx, dy):
                assert gl(w_out, t + 30) == translate(O, dx, dy)
                din = DN[glider_worldline(I, 0)[0]]
                dout = DN[glider_worldline(O, 0)[0]]
                found.append({'image_k': k, 'lean_stage': 'rf0%s%s' % (din, dout), 'translation': [dx, dy],
                              'start_time': t, 'start_time_mod30': t % 30})
    assert len(found) == 1, (piece, found)
    return found[0]


def body(kind):
    U = p0_parts.UnitLP(kind, 2)
    bp, w_in, outs = l1_parts.body(kind)
    cin = wl_out(l1_parts.OR_OUT, U.gates[0])
    d = cin[2] - w_in[2]
    bp = [move(p, 0, 0, d) for p in bp]
    outs = {k: mwl(w, 0, 0, d) for k, w in outs.items()}
    assert mwl(w_in, 0, 0, d) == cin
    for p in bp:
        assert p in U.pieces
    res = {'kind': kind, 'frame': 'unit template local frame (last entry copy = (asm, 0, 0, 0, 0) at the origin); the unit is moved to the layout by a translation only (no delay)',
           'chain_output': wl_s(cin), 'stages': [], 'rf_matches': {}}
    names = 'F_B + F_A' if kind == 'dec' else 'F_A'
    order = ['L', 'R', 'D'] if kind == 'dec' else ['R', 'D']
    raw = [outs[k] for k in order]
    # timeline: when each raw output is free of the fan-out pieces, when it reaches its first RF0
    FE = Env(envset(bp, set()))
    fb = bbox(envset(bp, set()))
    first_rf = {}
    for k in order:
        g = outs[k]
        if k in ('L', 'R'):
            first_rf[k] = reflect(g, SE, coord_of(U.cols[k]))[0]
        elif kind == 'dec':
            first_rf[k] = reflect(g, NE, lane_of(NE, p0_parts.JOG_V))[0]
    timeline = {}
    for k, w in zip(order, raw):
        t_free = approach(FE, w, time_at(w, ((fb[0] + fb[2]) / 2, (fb[1] + fb[3]) / 2)), span=3500)[2]
        t_hit = None
        if k in first_rf:
            RE = Env(env_cells(first_rf[k]))
            t = t_free
            while RE.dist(gl(w, t)) >= 3:
                t += 1
            t_hit = t
        timeline[k] = {'free_of_fanout_pieces_from': t_free, 'within_3_of_its_RF0_at': t_hit}
    tf = max(v['free_of_fanout_pieces_from'] for v in timeline.values())
    th = min([v['within_3_of_its_RF0_at'] for v in timeline.values() if v['within_3_of_its_RF0_at'] is not None])
    res['timeline'] = timeline
    res['fanout_then_reflectors_sequential'] = tf < th
    print(kind, 'timeline', timeline, 'sequential', tf < th, flush=True)
    f = make_fact('%s_fanout' % kind, bp, set(), [cin], raw, None, kind='stage_multi_out', span=3500, limit=6000, extra={
        'note': 'fan-out %s: one input (the chain output), outputs %s (raw lines before the turning RF0s)' % (names, order),
        'out_names': order})
    res['stages'].append(f)
    # the RF0 stages
    turns = [p for p in U.pieces if p[0] == 'rf']
    final = {}
    chainrf = []
    for k in order:
        g = outs[k]
        if k in ('L', 'R'):
            rf, g2 = reflect(g, SE, coord_of(U.cols[k]))
            chainrf.append((k, [(rf, g, g2)]))
            final[k] = g2
        elif kind == 'dec':
            rf1, g1 = reflect(g, NE, lane_of(NE, p0_parts.JOG_V))
            rf2, g2 = reflect(g1, SE, lane_of(SE, p0_parts.JOG_U))
            chainrf.append((k, [(rf1, g, g1), (rf2, g1, g2)]))
            final[k] = g2
        else:
            final[k] = g
    allrf = [x[0] for _, lst in chainrf for x in lst]
    assert sorted(allrf) == sorted(turns), (allrf, turns)
    for k, lst in chainrf:
        for i, (rf, gi, go) in enumerate(lst):
            m = match_rf(rf, gi, go)
            nm = '%s_rf_%s%d' % (kind, k, i)
            fr = make_fact(nm, [rf], set(), [gi], [go], None, kind='stage', span=600, extra={'rf_image_match': m,
                           'note': 'RF0 turning output %s; equals the certified image stage %s translated by %s, started at local time %d' % (k, m['lean_stage'], m['translation'], m['start_time'])})
            res['stages'].append(fr)
            res['rf_matches'][nm] = m
    # a sequential decomposition: stage A = fan-out + every RF0 reached before all outputs are free
    if not res['fanout_then_reflectors_sequential']:
        chains = dict(chainrf)
        cur = {k: outs[k] for k in order}
        nxt = {k: 0 for k in order}
        incl = []
        tf = max(v['free_of_fanout_pieces_from'] for v in timeline.values())

        def hit(k):
            lst = chains.get(k, [])
            if nxt[k] >= len(lst):
                return None
            rf = lst[nxt[k]][0]
            RE = Env(env_cells(rf))
            t = 0
            while RE.dist(gl(cur[k], t)) >= 3:
                t += 1
            tt = approach(RE, cur[k], t, span=400)
            first = min(x for x in range(t - 400, t + 400) if RE.dist(gl(cur[k], x)) < 3)
            return first
        changed = True
        while changed:
            changed = False
            for k in order:
                h = hit(k)
                if h is not None and h < tf:
                    rf, gi, go = chains[k][nxt[k]]
                    incl.append(rf)
                    nxt[k] += 1
                    cur[k] = go
                    tf = max(tf, approach(Env(env_cells(rf)), go, h, span=400)[2])
                    changed = True
        nh = [h for h in (hit(k) for k in order) if h is not None]
        fa = make_fact('%s_stageA' % kind, bp + incl, set(), [cin], [cur[k] for k in order], None, kind='stage_multi_out', span=3500,
                       limit=6000, t_min_out=tf, extra={
                           'note': 'first stage of a sequential decomposition: %s + the RF0s %s (reached before every output is free); outputs %s; the remaining RF0s are separate stages' % (names, incl, order),
                           'out_names': order, 'included_rf': [list(p) for p in incl],
                           'remaining_rf_first_contact_times': nh})
        assert fa['t0'] + fa['Delta'] < min(nh), 'stage A overlaps a later RF0'
        res['stageA'] = fa
        res['stageA_remaining'] = [list(p) for p in turns if p not in incl]
    # whole body in one run
    fin = [final[k] for k in order]
    allp = bp + turns
    f = make_fact('%s_body_whole' % kind, allp, set(), [cin], fin, None, kind='stage_multi_out', span=4000, limit=8000, extra={
        'note': 'the whole body (%s + %d RF0) as one reaction: chain output -> the unit outputs %s (columns)' % (names, len(turns), order),
        'out_names': order})
    res['whole'] = f
    # separation of the fan-out outputs from the turning RF0s at the end of the fan-out stage
    fo = res['stages'][0]
    tD = fo['t0'] + fo['Delta']
    E = Env(set().union(*[env_cells(p) for p in turns])) if turns else None
    res['fanout_out_to_rf_env'] = {k: E.dist(gl(w, tD)) for k, w in zip(order, raw)} if E else None
    # consistency with the template I/O table (p0_units.json): same lines, one common time shift
    Ut = p0_parts.unit(kind, 2)
    io = Ut.io[0]
    shifts = {k: io[k][2] - final[k][2] for k in order}
    assert all(io[k][:2] == final[k][:2] for k in order) and len(set(s % 30 for s in shifts.values())) == 1, (io, final)
    assert len(set(shifts.values())) == 1, shifts
    res['template_io_shift'] = list(shifts.values())[0]
    res['final_outputs'] = {k: wl_s(final[k]) for k in order}
    return res


def main():
    out = {'dec': body('dec'), 'inc': body('inc')}
    json.dump(out, open(os.path.join(CRES, 'cat_bodies.json'), 'w'))


if __name__ == '__main__':
    main()
