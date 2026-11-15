#!/usr/bin/env python3
"""P6 (R-31): the catalogue of distinct local certificates used by LP(program) for the given programs:
route reflectors by image (in direction -> out direction) and relative phase (the phase of the RF0
copy minus the arrival time of its glider, mod 30), window inputs by (receiving gate, residue), token
deltas, unit templates.  Usage: p6_catalogue.py add share rand   (results/p6_catalogue.txt)"""
import sys
from lpcommon import *
from net import RF_IMG
import p1_layout as P1


def main():
    names = sys.argv[1:] or ['add', 'share', 'rand']
    out = open(os.path.join(LPRES, 'p6_catalogue.txt'), 'w')

    def log(s=''):
        print(s, flush=True)
        out.write(s + '\n')
    rf, win, tok, units = {}, {}, {}, set()
    for nm in names:
        m = P1.layout([tuple(x) for x in P1.get_prog(nm)])
        for L in m.links:
            for p, g in zip(L['pieces'], L['legs'][:-1]):
                k = p[1]
                i0, o0 = RF_IMG[k]
                # relative phase: piece delay - (arrival tau of g relative to the image's input tau), mod 30
                rel = (p[4] - (g[2] - i0[2] + 4 * i0[0][0] * p[2])) % 30
                key = (k, '%s->%s' % (wl((i0[0], 0, 0))[1:3], wl((o0[0], 0, 0))[1:3]), rel)
                rf[key] = rf.get(key, 0) + 1
            if 'rho' in L:
                gate = 'OR gate (entry copy)' if L['dst'][0] == 'unit' else ('OR gate (DEC chain copy)' if L['kind'] == 'C' else 'OR gate (INC chain copy)')
                res = (L['final'][2] - L['wlo'][2]) % 30
                win[(gate, res)] = win.get((gate, res), 0) + 1
            if 'delta' in L:
                tok[(L['kind'], L['delta'])] = tok.get((L['kind'], L['delta']), 0) + 1
        for a, d in enumerate(m.UN):
            if d['used']:
                units.add((d['kind'], d['T'].n))
    log('route reflectors (RF0 image k, turn, relative phase): uses')
    for key in sorted(rf):
        log('  image %d %-9s phase %2d: %d' % (key[0], key[1], key[2], rf[key]))
    log('distinct (image, phase): %d' % len(rf))
    log('window inputs (gate, residue relative to the window base tau_t; R-29 numbering = residue + 1): uses')
    for key in sorted(win):
        log('  %-26s residue %2d: %d' % (key[0], key[1], win[key]))
    log('token deltas (station capture certificates): %s' % tok)
    log('unit templates used: %s' % sorted(units))


if __name__ == '__main__':
    main()
