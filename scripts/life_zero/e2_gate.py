#!/usr/bin/env python3
"""E2 (R-27): the NZ gate G_N.  A copy of blockedStream placed on the detector's onward path (NE of
the register of REG1, world frame) that, controlled by the detector D (case NZ), releases TWO
stream gliders N1, N2 (one lane, 30 apart; catalogue of scripts/life_gates, records of kind
'other' with two equal outputs).  N1 is the NZ output; N2 will kill the unconditional glider O.

World frame of REG1: D = shift(local (NE, -10, 19)) = (NE, -398, 1159).  For every record, every
symmetry mapping its control direction to NE and every position j (cells along D's path beyond the
register), filters: envelope >= 40 from the REG1 envelope, >= 25 from the register blocks
B_-1 .. B_80, N1 / N2 lines >= 25 from REG1 and >= 8 from the gate's own envelope downstream.
Candidates are simulated (Net.react, set simulator).  Output: results/e2_gate.json"""
import json
import os
import sys
from dcat import *
from common import life, bbox
from machine import load_catalog, wl_map
from net import Net, env_cells, glider_path, set_dist, piece_cells, box_dist
REGF = os.path.join(HERE, '..', 'life_machine', 'results', 'register.json')
DW = (NE, -398, 1159)
if __name__ == '__main__' and len(sys.argv) > 3:
    DW = ({'SW': SW, 'NE': NE}[sys.argv[1]], int(sys.argv[2]), int(sys.argv[3]))
REG = (155, 251)


def reg_env():
    d = json.load(open(REGF))
    pieces = [tuple(p) for p in d['pieces']]
    e = set()
    for p in pieces:
        e |= env_cells(p)
    return pieces, e


def place(ctrl, k, target, j):
    """piece (asm, k, vx, vy, s) whose image of the control world line ctrl is target; j = position."""
    w0 = wl_map(ctrl, (k, 0, 0, 0))
    d = w0[0]
    assert d == target[0]
    # translation (p, q) along the target lane: lane0 + d1 p - d0 q = L
    p = j
    num = w0[1] + d[1] * p - target[1]
    if num % d[0]:
        return None
    q = num // d[0]
    s = (target[2] - (w0[2] - 4 * d[0] * p)) % 30
    asm = (k, p, q, s)
    w = wl_map(ctrl, asm)
    if w[:2] != target[:2] or (w[2] - target[2]) % 30:
        return None
    return asm, (target[2] - w[2])


if __name__ == '__main__':
    pieces, E = reg_env()
    EB = bbox(E)
    blocks = set()
    for kk in range(-1, 81):
        blocks |= translate(set(counter(kk)), 148, 240)
    EN, BN = Near(E), Near(blocks)
    AVOID = None
    if os.environ.get('E2_AVOID_R'):
        # the restore glider R of the Z branch: (NE, -408) world, the whole line near the register
        rw = (NE, -408, 0)
        AVOID = Near(glider_path(rw, int(time_at(rw, (155, 251))) - 2400, int(time_at(rw, (155, 251))) + 400))
    if os.environ.get('E2_RFR_J'):
        # the reflector RF_R of the Z restore (e8_rfr.py) and the paths of R and of its input
        rr = [r for r in json.load(open(os.path.join(HERE, 'results', 'e8_rfr.json'))) if r['j'] == int(os.environ['E2_RFR_J'])][0]
        rfp = tuple(rr['rf'])
        Rw = (tuple(rr['R'][0]), rr['R'][1], rr['R'][2])
        Rin = (tuple(rr['Rin'][0]), rr['Rin'][1], rr['Rin'][2])
        ce = env_cells(rfp)
        tr = int(time_at(Rw, (rfp[2], rfp[3])))
        av = ce | glider_path(Rw, tr, int(time_at(Rw, (155, 253)))) | glider_path(Rin, tr - 2400, tr)
        AVOID = Near(av)
    recs = load_catalog()
    cands = []
    for r in recs:
        if not (r['kind'] == 'other' and r['from_infinity'] and len(r['outs']) == 2):
            continue
        nm = [x[1] for x in r['outs']]
        ws = sorted(x[0] for x in r['outs'])
        if not (nm[0] == nm[1] and ws[0][:2] == ws[1][:2] and ws[1][2] - ws[0][2] == 30):
            continue
        for k in range(8):
            if life.sym_apply(k, r['d']) != DW[0]:
                continue
            for j in range(60, 600, 4):
                pl = place(r['wl'], k, DW, REG[0] + (j if DW[0] == NE else -j))
                if pl is None:
                    continue
                asm, dt = pl
                piece = ('asm',) + asm
                env = env_cells(piece)
                if EN.dist(env, 40) < 40:
                    continue
                if BN.dist(env, 25) < 25:
                    continue
                if AVOID is not None and AVOID.dist(env, 12) < 12:
                    continue
                outs = [wl_map(w, asm) for w in ws]
                outs = [shift_wl(w, 0, 0, dt) for w in outs]
                tc = time_at(outs[0], rf_pt) if False else None
                ok = True
                for w in outs:
                    b = bbox(env)
                    cen = ((b[0] + b[2]) / 2, (b[1] + b[3]) / 2)
                    t0 = int(time_at(w, cen))
                    path = glider_path(w, t0 + 60, t0 + 1500)
                    pb = bbox(path)
                    if EN.dist(path, 25) < 25 or Near(env).dist(path, 8) < 8 or BN.dist(path, 10) < 10 or (AVOID is not None and AVOID.dist(path, 10) < 10):
                        ok = False
                        break
                if ok:
                    cands.append((r['wl'], k, j, piece, outs))
                    break
    print('candidates passing the filters:', len(cands), flush=True)
    good = []
    cands.sort(key=lambda c: c[2])
    for (cw, k, j, piece, outs) in cands[:12]:
        nt = Net([piece])
        st, got, Ts, Te = nt.react([DW], limit=3000, t_hint=1200)
        if st == 'ok' and sorted(got) == sorted(outs):
            good.append({'piece': list(piece), 'j': j, 'outs': [[list(w[0]), w[1], w[2]] for w in outs],
                         'Ts': Ts, 'Te': Te})
            print('  G_N', piece, 'j', j, '-> N1, N2', [(DIRNAME[w[0]],) + w[1:] for w in outs], 'Ts', Ts, 'Te', Te, flush=True)
        else:
            print('  fails', piece, st, flush=True)
    json.dump(good, open(os.path.join(HERE, 'results', 'e2_gate.json'), 'w'))
