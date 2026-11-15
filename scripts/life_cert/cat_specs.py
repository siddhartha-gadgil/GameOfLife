#!/usr/bin/env python3
"""Collect the 13 remaining R-31 catalogue entries (8 station facts, 2 unit bodies, 3 module
operations) from results/cat_stations.json, cat_bodies.json, cat_module.json (written by
cat_stations.py, cat_bodies.py, cat_module.py, which verify every fact by exact simulation) into
results/cat_specs.json.  Usage: cat_specs.py"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')
ST = json.load(open(os.path.join(RES, 'cat_stations.json')))
BO = json.load(open(os.path.join(RES, 'cat_bodies.json')))
MO = json.load(open(os.path.join(RES, 'cat_module.json')))

CONV = {
    'cells': '(x, y), y down, world frame of REG1 (stations, module) or the unit template frame (bodies)',
    'window': 'ofRows x0 y0 rows: bit j of rows[i] is the cell (x0 + j, y0 + i); rows above 2^53 are given as decimal strings',
    'world_line': '(dir, lane, tau) as scripts/life_gates/life.glider_at: dir in SE/SW/NW/NE, lane = dy*x - dx*y, the glider is the canonical phase at x = dx*q at time tau + 4 q; a glider (d, lane, tau + s) is the same glider s generations later',
    'pieces': "('asm', k, x, y, s) = blockedStream (the OR gate piece), ('rf', k, x, y, s) = RF0, symmetry k, translated, delayed by s (scripts/life_machine/net.piece_cells)",
    'G': 'the union of the pieces at time t0 (t0 = 0 mod 30, so every piece is at phase 0 of the common clock) and the eater cells; period 30 checked',
    'B': 'bounding box of G over its 30-cycle (xmin, ymin, xmax, ymax); Lean Box xmin xmax ymin ymax',
    'R': 'hull of the bounding boxes of the exact evolution of G u In over [t0, t0 + Delta] and of B (R_tight: without B; B_in_R_tight says whether hull was needed)',
    'equation': 'evolve Delta (G u In) = (pieces at t0 + Delta) u Out, i.e. phase G Delta u Out; In and Out at Chebyshev distance >= 3 from the whole envelope (all phases) of the pieces',
}


def strip(f):
    return f


def main():
    facts = {f['name']: f for f in ST['facts']}
    cat = []
    for nm, title in (('capture_NZ', 'capture NZ (delta = 0)'), ('capture_Z', 'capture Z (delta = -1)'),
                      ('pass_NZ', 'pass NZ'), ('pass_Z', 'pass Z'),
                      ('unpaired_token_NZ', 'unpaired token NZ'), ('unpaired_token_Z', 'unpaired token Z'),
                      ('line_end_NZ', 'line end NZ'), ('line_end_Z', 'line end Z')):
        f = dict(facts[nm])
        line = f['station']
        rel = ST['relations'][line]
        f['catalogue_entry'] = 'dispatch station: ' + title
        f['stage_format'] = 'Stage' if f['kind'] == 'stage' else 'reaction (two inputs and/or Out = empty)'
        f['translation_rule'] = (
            'station j (j < D) = this fact translated by (72 j, %d j) with all times + 288 j (pieces, eater, token, X, output: checked for j < %d)'
            % (rel['translation_per_station'][1], rel['stations_checked'])
            if not nm.startswith('line_end') else ST['relations']['line_end'])
        f['time_rule'] = "all times + 30 m when C' is (SE, 41, 4444 + 30 m) (the layout's C' slot)"
        cat.append(f)
    for kind in ('dec', 'inc'):
        b = BO[kind]
        st = {s['name']: s for s in b['stages']}
        e = {'name': 'unit_body_%s' % kind, 'catalogue_entry': 'unit body %s' % kind, 'kind': 'unit body',
             'frame': b['frame'], 'chain_output_input': b['chain_output'], 'final_outputs': b['final_outputs'],
             'template_io_shift': b['template_io_shift'], 'timeline': b['timeline'],
             'fanout_then_reflectors_sequential': b['fanout_then_reflectors_sequential'],
             'rf_matches': b['rf_matches'], 'whole_body_fact': b['whole']}
        if b['fanout_then_reflectors_sequential']:
            seq = [st['%s_fanout' % kind]] + [s for n, s in st.items() if '_rf_' in n]
            e['sequential_stages'] = seq
        else:
            remaining = b['stageA_remaining']
            seq = [b['stageA']] + [s for n, s in st.items() if '_rf_' in n and s['pieces'][0] in remaining]
            e['sequential_stages'] = seq
            e['fanout_alone_fact (not composable in time, kept for reference)'] = st['%s_fanout' % kind]
        e['other_rf_stage_facts'] = [s for n, s in st.items() if '_rf_' in n and s not in seq]
        cat.append(e)
    runs = MO['module_runs']
    ch = MO['chains']
    mods = MO['modules']
    common = {'gen_relation': MO['gen_relation'], 'module_contents_D1_D2_D3': mods}
    cat.append({'name': 'module_DEC_k0', 'catalogue_entry': "register module: DEC from C', k = 0 (Z)", 'kind': 'module operation (interface)',
                'certified_core': 'dz2mk0Run_rest (Gen/Dz2mk0Run.lean): Lean time 0 = world time -300 + 30 m; 27540 generations; block 0 stays; output X_Z',
                'input': "C' = (SE, 41, 4444 + 30 m) (from the DEC chain: see DEC_chain)",
                'output': 'X_Z = %s (+30 m): passes Z stations 0 .. j-1 (pass_Z), captured at Z station j with its token (capture_Z); the NZ token of caller j is absorbed (unpaired_token_NZ)' % (ST['X_Z'],),
                'DEC_chain': ch, 'whole_module_runs': [r for r in runs if r['op'] == 'dec' and r['k'] == 0], **common})
    cat.append({'name': 'module_DEC_k_ge1', 'catalogue_entry': "register module: DEC from C', k >= 1 (NZ)", 'kind': 'module operation (interface)',
                'certified_core': 'dz2gAll k (k >= 2) and dz2mk1Run_rest (k = 1) (Gen/Dz2gRun.lean, Dz2mk1Run.lean): Lean time 0 = world time -300 + 30 m; 4 k + 11490 generations; block k -> k - 1; output X_NZ',
                'input': "C' = (SE, 41, 4444 + 30 m)",
                'output': 'X_NZ = %s (+30 m), independent of k: passes NZ stations 0 .. j-1 (pass_NZ), captured at NZ station j (capture_NZ); the Z token is absorbed (unpaired_token_Z)' % (ST['X_NZ'],),
                'DEC_chain': ch, 'whole_module_runs': [r for r in runs if r['op'] == 'dec' and r['k'] >= 1], **common})
    cat.append({'name': 'module_INC', 'catalogue_entry': 'register module: INC through G_I', 'kind': 'module operation (interface)',
                'certified_core': 'dz2iAll k (Gen/Dz2iRun.lean): Lean time 0 = world time 2970 + 30 m for the control (NE, 1910, 6390 + 30 m); 4 k + 6990 generations; block k -> k + 1; no output',
                'input': 'INC port (merge link) -> INC chain (1 OR gate) -> RF_J -> G_I side input',
                'INC_chain': ch['INC'], 'GI_bridge': ch['GI'],
                'whole_module_runs': [r for r in runs if r['op'] == 'inc'], **common})
    out = {'conventions': CONV, 'catalogue': cat,
           'station_relations': ST['relations'], 'X_NZ': ST['X_NZ'], 'X_Z': ST['X_Z'], 'Cprime_ref': ST['Cprime_ref']}
    p = os.path.join(RES, 'cat_specs.json')
    json.dump(out, open(p, 'w'), separators=(',', ':'))
    print('wrote', p, os.path.getsize(p), 'bytes;', len(cat), 'entries')


if __name__ == '__main__':
    main()
