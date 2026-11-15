#!/usr/bin/env python3
"""The 3 register-module operations of the R-31 catalogue: exact interface (untrusted extractor).

M(D) = l0_module.module(D) (R-30 / R-31): R-29's circuit (REG1 + DZ2' + G_I = the pieces of the
certified runs dz2g / dz2mk0 / dz2mk1 / dz2i, LeanTheory/Theory/Life/Gen) + RF_J + INC chain
(1 OR gate) + DEC chain (2 D OR gates) + D stations per answer line + their eaters + 2 line-end
eaters.  Checks (exact):
  (1) the Gen data dz2gR*, dz2mk0R*, dz2mk1R*, dz2iR* (parsed from Lean) = R-29's circuit at the
      plan start time Ts; the Lean input / output gliders = the world lines used here;
  (2) DEC chain: side input of copy t (every R-29 residue 1..13) -> C' = (SE, 41, .) (chain alone);
  (3) INC chain + RF_J: side input of the INC copy -> the G_I control of dz2i (alone);
  (4) whole module M(D) from the port input, tokens of caller j (NZ delta 0, Z delta -1):
      DEC k = 0 -> block 0 + the glider dispatched at Z station j; DEC k >= 1 -> block k - 1 + the
      glider dispatched at NZ station j; INC -> block k + 1; nothing else; everything back in cycle.
Usage: cat_module.py [quick]  -> results/cat_module.json"""
import json
import re
from cat_common import *  # noqa
import g9_dispatch as G9

GEN = os.path.join(CHERE, '..', '..', 'LeanTheory', 'Theory', 'Life', 'Gen')
DD = dz2()[1]
CTRL_INC = ((1, -1), 1910, 6390)


def lean_rest(prefix):
    s = open(os.path.join(GEN, prefix[0].upper() + prefix[1:] + 'Data.lean')).read()
    cells = set()
    n = 0
    for m in re.finditer(r'def %sR(\d+) : Finset Cell :=\s*ofRows \(?(-?\d+)\)? \(?(-?\d+)\)?\s*\[([^\]]*)\]' % prefix, s):
        rows = [int(x) for x in m.group(4).replace('\n', ' ').split(',')]
        cells |= cells_of_window(int(m.group(2)), int(m.group(3)), rows)
        n += 1
    assert n == 28, (prefix, n)
    return cells


def ofr(x, y, rows):
    return set(cells_of_window(x, y, rows))


def main():
    quick = len(sys.argv) > 1
    out = {}
    M1 = L2.mod(1)
    base = l0_module.base()[0]
    # ---------------- (1) relation to the Gen certificates -----------------------------------
    rel = {}
    for prefix, Ts in (('dz2g', -300), ('dz2mk0', -300), ('dz2mk1', -300), ('dz2i', 2970)):
        L = lean_rest(prefix)
        assert L == gcells(base, set(), Ts), prefix
        rel[prefix] = {'Rest_equals_R29_circuit_at_world_time': Ts}
    CP = DD['ctrl']
    assert gl(CP, -300) == ofr(-1186, -1227, [2, 4, 7])
    assert gl(DD['n1'], -300 + 11490) == ofr(603, 994, [1, 6, 3])
    assert gl(DD['zout'], -300 + 27540) == ofr(4562, -4025, [3, 6, 1])
    assert gl(CTRL_INC, 2970) == ofr(-855, -1055, [7, 4, 2])
    for k in (-1, 0, 1, 5):
        assert set(block(k)) == translate(set(counter(k)), 148, 240)
    assert set(block(0)) == ofr(155, 251, [3, 3]) and set(block(1)) == ofr(156, 252, [3, 3])
    rel['time_alignment'] = (
        "Lean time 0 of dz2gAll / dz2mk0Run_rest / dz2mk1Run_rest = module world time -300 + 30 m when "
        "C' = (SE, 41, 4444 + 30 m) (C' at time -300 = ofRows (-1186) (-1227) [2, 4, 7]); Lean time 0 of "
        "dz2iAll = world time 2970 + 30 m when the G_I control is (NE, 1910, 6390 + 30 m) (at time 2970: "
        "ofRows (-855) (-1055) [7, 4, 2]).  dz2gRest etc. = R-29's circuit (REG1 + DZ2' + G_I, %d pieces) at "
        "that time (checked cell-equal from the Lean data).  reg1Block k = translate (148, 240) (counter k)." % len(base))
    rel['outputs'] = {
        'NZ (k >= 1)': "dz2gAll (k >= 2) / dz2mk1Run_rest (k = 1): the glider translate (k, k) (ofRows 603 994 [1, 6, 3]) at Lean time 4 k + 11490 = world line X_NZ = %s (+30 m), independent of k" % wl(DD['n1']),
        'Z (k = 0)': "dz2mk0Run_rest: ofRows 4562 (-4025) [3, 6, 1] at Lean time 27540 = world line X_Z = %s (+30 m); block 0 unchanged" % wl(DD['zout']),
        'INC': 'dz2iAll: no output glider; block k -> k + 1 in 4 k + 6990 generations'}
    out['gen_relation'] = rel
    # ---------------- module contents --------------------------------------------------------
    mods = {}
    for D in (1, 2, 3):
        M = L2.mod(D)
        P = set(M['pieces'])
        assert set(base) <= P
        extra = [p for p in M['pieces'] if p not in base]
        nz, zs = G9.line_stations(6, DD['n1'], (450, 841), D), G9.line_stations(5, DD['zout'], (900, -363), D)
        mods[D] = {
            'pieces_total': len(M['pieces']), 'R29_circuit_pieces': len(base),
            'extra_pieces': [list(p) for p in extra],
            'RF_J': list(l0_module.base()[2]),
            'INC_chain': [list(g) for g in M['inc_gates']],
            'DEC_chain (copy 0 = upstream .. 2D-1 feeds DZ2)': [list(g) for g in M['dec_gates']],
            'NZ_stations (gate, RF_S)': [[list(s[0]), list(s[1])] for s in nz],
            'Z_stations (gate, RF_S)': [[list(s[0]), list(s[1])] for s in zs],
            'eater_cells': win(set(M['eaters'])), 'eater_count_cells': len(M['eaters']),
            'DEC_ports (side input copy t, residue 1 = this tau; window tau..tau+12, + 30 m)': [wl_s(w) for w in M['dec']],
            'INC_port': [wl_s(w) for w in M['inc']],
            'tokens (timed for C\' = (SE, 41, 4444); NZ delta 0, Z delta -1 in R-31)': {
                'NZ': [wl_s(K) for K, S in M['nz']], 'Z': [wl_s(K) for K, S in M['z']]},
            'dispatched (nominal)': {'NZ': [wl_s(S) for K, S in M['nz']], 'Z': [wl_s(S) for K, S in M['z']]},
            'uvbox': list(M['uvbox']),
        }
        # the DEC chain is a relay chain of the OR gate: copy t + 1 = copy t translated by (35, 64)
        dg = M['dec_gates']
        for t in range(len(dg) - 1):
            assert (dg[t + 1][2] - dg[t][2], dg[t + 1][3] - dg[t][3]) == (35, 64) and dg[t][1] == 0
    out['modules'] = mods
    # ---------------- (2) DEC chain alone, (3) INC chain + RF_J alone ------------------------
    chains = {}
    for D in (1, 2):
        M = L2.mod(D)
        dg = M['dec_gates']
        res = []
        for t in range(len(dg)):
            outs = {}
            for r in range(1, 14):
                w = mwl(M['dec'][t], 0, 0, r - 1 + 600)
                t0 = 30 * ((int(time_at(w, cross(dg[t]))) - 200) // 30)
                cells, rem = run_peel(dg, [w], t0, t0 + 3000, cbox=core_box(dg, margin=60))
                assert cells == gcells(dg, set(), t0 + 3000) and len(rem) == 1 and rem[0][:2] == CP[:2], (D, t, r, rem)
                assert (rem[0][2] - CP[2]) % 30 == 0
                outs[r] = rem[0][2] - (600 + 0)
            assert len(set(outs.values())) == 1, outs
            res.append({'copy': t, 'port_residue1_wl': wl_s(M['dec'][t]),
                        'Cprime_tau_for_port_tau_plus_r_minus_1 (any r in 1..13)': outs[1],
                        'formula': "port glider (NE, %d, %d + (r - 1) + 30 m), r = 1..13 -> C' = (SE, 41, %d + 30 m)" % (M['dec'][t][1], M['dec'][t][2], outs[1])})
        chains['DEC_D%d' % D] = res
        print('DEC chain D=%d' % D, [x['formula'] for x in res], flush=True)
    M = M1
    ig = M['inc_gates'] + [l0_module.base()[2]]
    resi = {}
    for r in range(1, 14):
        w = mwl(M['inc'][0], 0, 0, r - 1 + 600)
        t0 = 30 * ((int(time_at(w, cross(ig[0]))) - 200) // 30)
        cells, rem = run_peel(ig, [w], t0, t0 + 3000, cbox=core_box(ig, margin=60))
        assert cells == gcells(ig, set(), t0 + 3000) and len(rem) == 1 and rem[0][:2] == CTRL_INC[:2], (r, rem)
        resi[r] = rem[0][2] - 600
    assert len(set(resi.values())) == 1
    chains['INC'] = {'port_residue1_wl': wl_s(M['inc'][0]), 'pieces': [list(p) for p in ig],
                     'formula': 'port glider (NE, %d, %d + (r - 1) + 30 m), r = 1..13 -> INC OR gate -> RF_J -> G_I control (NE, 1910, %d + 30 m)' % (
                         M['inc'][0][1], M['inc'][0][2], resi[1])}
    print('INC', chains['INC']['formula'], flush=True)
    # G_I side input: the module's control (residue of RF_J's output) vs the control of dz2iAll
    GI = ('asm', 0, -843, -1143, 17)
    assert GI in base
    from net import wl_in
    cm = (CTRL_INC[0], CTRL_INC[1], resi[1])
    gi = {}
    for nm, c in (('module_control', cm), ('dz2i_control', CTRL_INC)):
        t0 = 30 * ((int(time_at(c, cross(GI))) - 200) // 30)
        cells, rem = run_peel([GI], [c], t0, t0 + 2000, cbox=core_box([GI], margin=60))
        assert cells == gcells([GI], set(), t0 + 2000) and len(rem) == 1
        gi[nm] = (c, rem[0])
    assert gi['module_control'][1][:2] == gi['dz2i_control'][1][:2] == DD['ci'][:2]
    dshift = gi['dz2i_control'][1][2] - gi['module_control'][1][2]
    assert dshift % 30 == 0
    facts = []
    for nm, (c, o) in gi.items():
        facts.append(make_fact('GI_side_' + nm, [GI], set(), [c], [o], None, kind='stage', extra={
            'gate_coords_input': wl_s(wl_in(c, GI)), 'gate_tau_mod30': wl_in(c, GI)[2] % 30,
            'note': 'G_I (an OR-gate copy, asm sym 0) side input; output = the DZ2 increment glider class ci = (SE, 314, .)'}))
    chains['GI'] = {'piece': list(GI), 'module_control': wl_s(cm), 'dz2i_control': wl_s(CTRL_INC),
                    'module_control_gate_coords': wl_s(wl_in(cm, GI)), 'dz2i_control_gate_coords': wl_s(wl_in(CTRL_INC, GI)),
                    'released_glider_module': wl_s(gi['module_control'][1]), 'released_glider_dz2i': wl_s(gi['dz2i_control'][1]),
                    'release_shift_dz2i_minus_module': dshift, 'facts': facts,
                    'note': 'the module drives G_I at a different side-window residue than dz2iAll; both release the same glider (SE, 314) up to 30 m, so dz2iAll applies to the module only after this bridge (a G_I side fact at the module residue + the dz2i run from the released glider on).'}
    print('GI', chains['GI']['module_control_gate_coords'], chains['GI']['dz2i_control_gate_coords'], dshift, flush=True)
    out['chains'] = chains
    # ---------------- (4) whole module runs --------------------------------------------------
    runs = []
    cases = [(1, 'dec', 0, 0), (1, 'dec', 1, 0), (1, 'dec', 2, 0), (1, 'inc', 0, None), (1, 'inc', 1, None),
             (2, 'dec', 0, 1), (2, 'dec', 1, 1)]
    if quick:
        cases = cases[:1]
    for D, op, k, j in cases:
        M = L2.mod(D)
        pieces, eaters = M['pieces'], set(M['eaters'])
        cb = core_box(pieces, [(140, 230, 900, 900), bbox(eaters)])
        evs = []
        if op == 'dec':
            t = 2 * j
            r = 5
            w = mwl(M['dec'][t], 0, 0, r - 1 + 30 * 400)
            cp_tau = chains['DEC_D%d' % D][t]['Cprime_tau_for_port_tau_plus_r_minus_1 (any r in 1..13)'] + 30 * 400
            sh = cp_tau - CP[2]
            assert sh % 30 == 0
            evs.append((30 * ((int(time_at(w, cross(M['dec_gates'][t]))) - 250) // 30), w))
            for nm, dl in (('nz', 0), ('z', -1)):
                K = M[nm][j][0]
                K = (K[0], K[1], K[2] + sh + dl)
                g = G9.line_stations(6, DD['n1'], (450, 841), D)[j][0] if nm == 'nz' else G9.line_stations(5, DD['zout'], (900, -363), D)[j][0]
                evs.append((30 * ((int(time_at(K, cross(g))) - 250) // 30), K))
            t_end = 30 * ((-300 + sh + (27540 if k == 0 else 11490 + 4 * k) + 2400 + 300 * D) // 30)
            kb = 0 if k == 0 else k - 1
            exp_line = (M['z'] if k == 0 else M['nz'])[j][1]
        else:
            w = mwl(M['inc'][0], 0, 0, 4 + 30 * 400)
            sh = resi[1] + 30 * 400 - CTRL_INC[2]
            evs.append((30 * ((int(time_at(w, cross(M['inc_gates'][0]))) - 250) // 30), w))
            t_end = 30 * ((2970 + sh + 6990 + 4 * k + 3000) // 30)
            kb = k + 1
            exp_line = None
        t0 = min(e[0] for e in evs)
        cells, rem = run_events(gcells(pieces, eaters | set(block(k)), t0), t0, evs, t_end, cb)
        want = gcells(pieces, eaters | set(block(kb)), t_end)
        ok = cells == want
        if exp_line is None:
            ok = ok and rem == []
        else:
            ok = ok and len(rem) == 1 and rem[0][:2] == exp_line[:2]
        assert ok, (D, op, k, j, rem, len(cells ^ want))
        runs.append({'D': D, 'op': op, 'k': k, 'caller_j': j, 'input': wl_s(w), 'events': [[e[0], wl_s(e[1])] for e in evs],
                     'Cprime_or_GI_shift_30m': sh, 't_end': t_end, 'block_after': kb,
                     'removed_gliders': [wl_s(x) for x in rem], 'ok': ok,
                     'removed_tau_minus_nominal_minus_shift': (rem[0][2] - exp_line[2] - sh) if exp_line else None})
        print('module run D=%d %s k=%d j=%s: removed %s ok' % (D, op, k, j, [wl(x) for x in rem]), flush=True)
    out['module_runs'] = runs
    json.dump(out, open(os.path.join(CRES, 'cat_module%s.json' % ('_quick' if quick else '')), 'w'))


if __name__ == '__main__':
    main()
