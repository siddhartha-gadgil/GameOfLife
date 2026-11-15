#!/usr/bin/env python3
"""The 8 dispatch-station facts of the R-31 catalogue (untrusted extractor; exact simulation).

Stations of the register module M(D) (l0_module.module / g9_dispatch.line_stations): NZ line
X_NZ = DZ2 output n1 (SE), gate symmetry 6; Z line X_Z = DZ2 output zout (NE), gate symmetry 5;
station j = station 0 translated by (72 j, 72 j) (NZ) resp. (72 j, -72 j) (Z) and delayed by 288 j.
Token world lines timed for C' = (SE, 41, 4444) (all shift by 30 m with C'); R-31 token delays:
NZ delta = 0, Z delta = -1 (token tau = nominal tau + delta).
Usage: cat_stations.py  -> results/cat_stations.json"""
import json
from cat_common import *  # noqa
import g9_dispatch as G9

DD = dz2()[1]
XN, XZ = DD['n1'], DD['zout']
DMAX = 3


def stations(D):
    nz = G9.line_stations(6, XN, (450, 841), D)
    zs = G9.line_stations(5, XZ, (900, -363), D)
    return nz, zs


def line_end(X, sts):
    Pm = sts[-1][5]
    far = (Pm[0] + 120 * X[0][0], Pm[1] + 120 * X[0][1])
    e = eater_absorbing(X, far)
    assert e
    return set(e)


def discover(pieces, eaters, ins, t0, n):
    cb = core_box(pieces, [bbox(eaters)] if eaters else [], margin=40)
    cells, rem = run_peel(pieces, ins, t0, t0 + n, extra=eaters, cbox=cb)
    assert cells == gcells(pieces, eaters, t0 + n), 'debris'
    return rem


def main():
    nz, zs = stations(DMAX)
    facts = []
    rel = {}
    # translation relation between stations j and 0 (pieces, eaters, tokens, dispatched gliders)
    for nm, sts, X, sg in (('NZ', nz, XN, 1), ('Z', zs, XZ, -1)):
        g0, rf0, E0, K0, S0, P0 = sts[0]
        for j in range(1, DMAX):
            g, rf, E, K, S, P = sts[j]
            dx, dy = 72 * j, sg * 72 * j
            for t in range(30):
                assert piece_cells(g, t + 288 * j) == translate(piece_cells(g0, t), dx, dy)
                assert piece_cells(rf, t + 288 * j) == translate(piece_cells(rf0, t), dx, dy)
            assert E == translate(E0, dx, dy)
            for w, w0 in ((K, K0), (S, S0), (X, X)):
                for t in (0, 7, 100):
                    assert gl(w, t + 288 * j) == translate(gl(w0, t), dx, dy)
        rel[nm] = {'translation_per_station': [72, 72 * sg], 'time_shift_per_station': 288,
                   'stations_checked': DMAX,
                   'stations': [{'j': j, 'gate': list(s[0]), 'RF_S': list(s[1]), 'eater_T': win(s[2]),
                                 'token_wl_nominal': wl_s(s[3]), 'dispatched_wl': wl_s(s[4]), 'meeting_point': list(s[5])}
                                for j, s in enumerate(sts)]}
    # line-end eaters for D = 1 .. DMAX: translations of the D = 1 eater
    ends = {}
    for D in range(1, DMAX + 1):
        n1, z1 = stations(D)
        ends[D] = (line_end(XN, n1), line_end(XZ, z1))
    for D in range(2, DMAX + 1):
        assert ends[D][0] == translate(ends[1][0], 72 * (D - 1), 72 * (D - 1))
        assert ends[D][1] == translate(ends[1][1], 72 * (D - 1), -72 * (D - 1))
    rel['line_end'] = 'line-end eater of M(D) = the D = 1 eater translated by (72 (D-1), +-72 (D-1)) (checked D <= %d); X arrives 288 (D-1) later' % DMAX
    tok_delta = {'NZ': 0, 'Z': -1}
    for nm, sts, X in (('NZ', nz, XN), ('Z', zs, XZ)):
        g, rf, E, K, S, P = sts[0]
        pcs = [g, rf]
        dl = tok_delta[nm]
        Kd = (K[0], K[1], K[2] + dl)
        tP = int(time_at(X, P))
        # capture
        t0 = 30 * ((tP - 700) // 30)
        out = discover(pcs, E, [Kd, X], t0, 1500)
        assert len(out) == 1, out
        assert out[0][:2] == S[:2]
        facts.append(make_fact('capture_%s' % nm, pcs, E, [Kd, X], out, tP, kind='reaction', extra={
            'station': nm, 'j': 0, 'token_delta': dl, 'token_wl_nominal': wl_s(K),
            'dispatched_equals_nominal_Sp': out[0] == S,
            'note': 'two inputs (token K, answer X); output the dispatched glider S\' (after RF_S). Station j: translate by (72 j, %d j), times + 288 j.' % (72 if nm == 'NZ' else -72)}))
        # pass (no token)
        outp = discover(pcs, E, [X], t0, 1500)
        assert outp == [X], outp
        Bx = cycle_box(pcs, E)
        cs = [time_at(X, (Bx[a], Bx[b])) for a in (0, 2) for b in (1, 3)]
        tpa, tpb = 30 * ((int(min(cs)) - 8) // 30), int(max(cs)) + 8
        facts.append(make_fact('pass_%s' % nm, pcs, E, [X], [X], tP, kind='stage', t0=tpa, t_min_out=tpb, extra={
            'min_dist_X_path_to_station_envelope': Env(envset(pcs, E)).dist(set().union(*[gl(X, t) for t in range(tpa, tpb)])),
            'station': nm, 'j': 0, 'note': 'the answer X passes a station without token unchanged (Out = In translated along the line)'}))
        # unpaired token
        outt = discover(pcs, E, [Kd], t0, 1500)
        assert outt == [], outt
        facts.append(make_fact('unpaired_token_%s' % nm, pcs, E, [Kd], [], tP, kind='reaction', extra={
            'station': nm, 'j': 0, 'token_delta': dl,
            'note': 'the token releases T, T is absorbed by the eater E_T; Out = empty'}))
    # line ends (D = 1)
    for nm, X, e in (('NZ', XN, ends[1][0]), ('Z', XZ, ends[1][1])):
        c = list(e)
        tc = time_at(X, (sum(x for x, y in c) / len(c), sum(y for x, y in c) / len(c)))
        facts.append(make_fact('line_end_%s' % nm, [], e, [X], [], tc, kind='reaction', extra={
            'station': nm, 'D': 1,
            'note': 'eater 1 at the end of the line absorbs X; Out = empty. For M(D): translate by (72 (D-1), %s72 (D-1)), times + 288 (D-1).' % ('' if nm == 'NZ' else '-')}))
    for f in facts:
        f['clock'] = "module world time; X = DZ2's answer for C' = (SE, 41, 4444) (shift everything by 30 m with C')"
    json.dump({'facts': facts, 'relations': rel, 'X_NZ': wl_s(XN), 'X_Z': wl_s(XZ), 'Cprime_ref': wl_s(DD['ctrl'])},
              open(os.path.join(CRES, 'cat_stations.json'), 'w'))


if __name__ == '__main__':
    main()
