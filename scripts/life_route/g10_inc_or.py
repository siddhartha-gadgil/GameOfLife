#!/usr/bin/env python3
"""G10 (R-29): the INC input lane 314 of REG1 shared by DZ2's internal C_I and external INC
instructions.

Obstruction: DZ2's reflector RF_C3 = ('rf', 7, -876, -1175, 11) emits DZ2's own C_I onto lane 314
(the INC input of REG1) from the NW; an OR gate releasing (SE, 314) has its gun A on lane 314
upstream of its crossing, i.e. in the way of RF_C3's glider, and an INC control from the far NW on
lane 314 would hit RF_C3.  Fix: an OR gate G_I (copy of the gate of g4_or.py) on lane 314 between
RF_C3 and REG1 whose THROUGH input is DZ2's C_I, re-emitted by RF_C3 moved along its input line
onto G_I's through lane; external INC controls use G_I's SIDE input.
For both gate symmetries that keep SE (0, 6) and every position of G_I along lane 314: RF_C3'
position, residue test of the through window, clearances (>= 15 to DZ2 / REG1 pieces).
Usage: g10_inc_or.py"""
import json
from gcommon import *
from net import reflect, reflect_to, RF_IMG, wl_out, wl_in, env_cells, env_box, box_dist, set_dist
from life import sym_apply

# SE -> SE relay records of the catalogue (results/g3_orcat.txt): through lane -> {tau residue: output tau}
RELAY = {}
for line in open(os.path.join(RES, 'g3_orcat.txt')):
    if line.startswith('SE lane'):
        a = line.split(':')
        L = int(a[0].split()[2])
        RELAY[L] = {int(x.split('->')[0]): int(x.split('->')[1].rstrip('?')) for x in a[1].split()}
PIECES, D = dz2()
RF_C3 = ('rf', 7, -876, -1175, 11)
CI = D['ci']                                  # (SE, 314, 22468)


def rf_c3_input():
    for j in range(-3000, 3000):
        p, w = reflect_to(CI, SW, j)
        if p == RF_C3:
            return w
    raise RuntimeError


def main():
    W = rf_c3_input()
    print('RF_C3 input %s, output %s' % (wl(W), wl(CI)))
    others = [p for p in PIECES if p != RF_C3]
    oenv = set()
    for p in others:
        oenv |= env_cells(p)
    from dcat import Near
    NO = Near(oenv)
    sols = []
    for k, TL in [(k, TL) for k in (0, 6) for TL in sorted(RELAY)]:
        T_WIN = RELAY[TL]
        tl = TL if k == 0 else -TL               # through lane / output lane in gate coords after sym
        ol = 14 if k == 0 else -14
        Lt = 314 + (tl - ol)
        r = reflect(W, SE, Lt)
        if r is None:
            print('sym %d, record lane %d: world through lane %d has the wrong parity for RF_C3' % (k, TL, Lt))
            continue
        rf, Wt = r
        print('sym %d, record lane %d: RF_C3\' = %s emits %s (distance to the other pieces %d)' % (k, TL, rf, wl(Wt), NO.dist(env_cells(rf), 64)))
        # gate positions along lane 314: translation (vx, vy) with vx - vy = 314 - ol
        ob = wl_out((SE, 14, 119), ('asm', k, 0, 0, 0))
        for a in range(rf[2] + 20, 0, 1):
            vx = a
            vy = a - (314 - ob[1])
            g0 = ('asm', k, vx, vy, 0)
            o0 = wl_out((SE, 14, 119), g0)
            assert o0[1] == 314, o0
            s = (CI[2] - o0[2]) % 30
            g = ('asm', k, vx, vy, s)
            # through input of the gate in gate coordinates
            wg = wl_in(Wt, g)
            if wg[0] != SE or wg[1] != TL:
                continue
            res = wg[2] % 30
            if res not in T_WIN:
                continue
            # the gate must be downstream of RF_C3' along the through line and clear
            de = NO.dist(env_cells(g), 64)
            dr = box_dist(env_box(g), env_box(rf))
            if de < 15 or dr < 15:
                continue
            # through segment from RF_C3' to the gate: clear of the others
            cx, cy = sym_apply(k, (45, 31))
            seg = glider_path(Wt, time_at(Wt, (rf[2], rf[3])) + 20, time_at(Wt, (cx + vx, cy + vy)))
            ds = NO.dist(seg, 64)
            if ds < 10:
                continue
            out = wl_out((SE, 14, wg[2] - res + T_WIN[res]), g)
            sols.append({'sym': k, 'lane': TL, 'gate': g, 'rf': rf, 'through': Wt, 'res': res, 'C_I': out, 'dist': [de, dr, ds]})
            print('  gate %s: through residue %d, new C_I %s, distances %d %d %d' % (g, res, wl(out), de, dr, ds), flush=True)
            break
    json.dump(sols, open(os.path.join(RES, 'g10_inc_or.json'), 'w'))


if __name__ == '__main__':
    main()
