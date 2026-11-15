#!/usr/bin/env python3
"""L5 (R-30): timing summary and export of a layout: results/l5_<program>.txt (table of links:
corners, reflectors, flight times, timing margins) and results/l5_<program>.json (all pieces,
eaters, register origins, start glider, halt line)."""
import sys
import json
from lcommon import *
import l2_layout as L2
from l3_check import PROGS


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'add'
    m = L2.layout(PROGS[name])
    out = open(os.path.join(RES, 'l5_%s.txt' % name), 'w')

    def log(s=''):
        print(s)
        out.write(s + '\n')

    log('program %s = %s' % (name, m.prog))
    log('registers %s: module u-shifts U_r %s (translation (U_r/2, -U_r/2)); band v %d .. %d; units at v %d' % (
        m.regs, m.U, m.V_T, m.V_B + 200, m.Vu))
    for key, d in m.UN.items():
        log('unit %-9s %-5s n=%d copies, origin uv (%d, %d) = xy %s; inputs %s%s' % (
            str(key), d['kind'], d['T'].n, d['A'], d['V'], d['dxy'], {str(k): v for k, v in d['copy'].items()},
            ('; outputs ' + str(d['assign'])) if 'assign' in d else ''))
    log()
    log('%-12s %6s %7s %7s %7s %5s %8s  %s' % ('link', 'h', 'H', 'c_src', 'c_dst', '#rf', 'flight', 'timing'))
    byname = {L['name']: L for L in m.links}
    for L in m.links:
        g0, g1 = L['legs'][0], L['final']
        pts = [((c[0] + c[1]) / 2, (c[1] - c[0]) / 2) for c in L['corners']]
        t_start = time_at(g0, pts[0])
        if L['dst'][0] == 'halt':
            info, fl = 'HALT line %s' % wl(g1), 0
        else:
            t_end = time_at(g1, cross(L['gate'])) if L.get('gate') else time_at(g1, pts[-1])
            fl = t_end - t_start
            if L['name'].endswith('.KNZ') or L['name'].endswith('.KZ'):
                i = int(L['name'][3:].split('.')[0])
                cp = m.UN[('I', i)]['cprime']
                r = m.prog[i][1]
                shift = cp[2] - m.port[(r, L['port'][1])]['ref'][2]
                target = mwl(m.port[L['port']]['line'], 0, 0, shift)
                info = 'token: tau - required tau = %d (window %s); C\' = %s' % (g1[2] - target[2], L2.TOK_W, wl(cp))
            else:
                slot = L2.window_slot(g1, L['wlo'])
                info = 'window residue %d of 0..12' % ((g1[2] - L['wlo'][2]) % 30)
                if 'done' in L:
                    info += '; arrives %d after DZ2 is done' % (time_at(g1, cross(L['gate'])) - L['done'])
                if 't_inc' in L:
                    info += '; arrives %d after the INC control reached the register' % (time_at(g1, cross(L['gate'])) - L['t_inc'])
        log('%-12s %6d %7s %7s %7s %5d %8d  %s' % (L['name'], L['h'], L['H'], L['csrc'], L['cdst'], len(L['pieces']), fl, info))
    # the unpaired-Z-token hazard after an NZ answer: the next C' on the same register comes after the
    # NZ answer has left the station; the unpaired Z token must have passed its station before the
    # Z output of that next call can reach the Z stations
    log()
    for i, ins in enumerate(m.prog):
        if ins[0] != 'dec':
            continue
        r = ins[1]
        cp = m.UN[('I', i)]['cprime']
        LZ, Ln = byname['dec%d.KZ' % i], byname['dec%d.nz' % i]
        Mr = m.mods[r]
        j = m.decs[r].index(i)
        st = Mr['stations']['z'][j][0]
        stw = move(st, m.U[r] // 2, -m.U[r] // 2)
        t_tok = time_at(LZ['final'], cross(stw))
        t_nz = time_at(Ln['legs'][0], cross(move(Mr['stations']['nz'][j][0], m.U[r] // 2, -m.U[r] // 2)))
        zout = L2.mw(m.U[r], Mr['D']['zout'])
        # next call's Z output reaches the first Z station at C'_2 + (time of zout at station 0 - C'(4444))
        st0 = move(Mr['stations']['z'][0][0], m.U[r] // 2, -m.U[r] // 2)
        lat = time_at(zout, cross(st0)) - time_at(L2.mw(m.U[r], Mr['CP']), (-1100 + m.U[r] // 2, -1100 - m.U[r] // 2))
        t_cp = time_at(cp, (-1100 + m.U[r] // 2, -1100 - m.U[r] // 2))
        log('dec %d: C\' passes F_B at %d; NZ answer leaves NZ station %d at %d (+%d); an unpaired Z token passes Z station %d at %d (+%d); '
            'a later call\'s Z output reaches the Z stations >= %d after its C\' passes F_B, i.e. here >= %d (margin %d)' % (
                i, t_cp, j, t_nz, t_nz - t_cp, j, t_tok, t_tok - t_cp, lat, t_nz + lat, t_nz + lat - t_tok))
    json.dump({'program': m.prog, 'pieces': m.pieces, 'names': m.names, 'eaters': sorted(m.eaters),
               'register_shift': {r: [m.U[r] // 2, -m.U[r] // 2] for r in m.regs},
               'block_k': 'translate (148 + U_r/2, 240 - U_r/2) (counter k)', 'start': [list(m.start[0]), m.start[1], m.start[2]],
               'start_time': m.start_t, 'halt_line': [list(m.halt[0]), m.halt[1], m.halt[2]]},
              open(os.path.join(RES, 'l5_%s.json' % name), 'w'))


if __name__ == '__main__':
    main()
