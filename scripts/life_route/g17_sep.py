#!/usr/bin/env python3
"""G17 (R-29): separations of the new pieces (DEC chain, G_I, RF_C3', RF_J, INC chain, dispatch
stations, eaters): envelope distances to all other pieces, to DZ2's flight trace (g16), to the
blocks B_-1..B_600, and the input lines (from 1500 cells away) to everything they do not use."""
import json
from gcommon import *
from net import env_cells, wl_out
from dcat import Near
import g16_trace
import g14_full as F

TR = Near(g16_trace.trace())
BL = Near(blocks(-1, 600))
envs = {p: env_cells(p) for p in F.PIECES}
names = {}
for p in F.base:
    names[p] = 'DZ2/REG1'
names[F.GI] = 'G_I'
names[F.RFJ] = 'RF_J'
for i, g in enumerate(F.INCC):
    names[g] = 'INC chain copy %d' % (i + 1)
for i, g in enumerate(F.DECC):
    names[g] = 'DEC chain copy %d' % (i + 1)
for i, p in enumerate(F.STATIONS):
    names[p] = 'station piece %d' % i
names[F.base[[i for i, p in enumerate(F.base) if p[0] == 'rf' and p[2:4] == (-863, -1188)][0]]] = "RF_C3'"
new = [p for p in F.PIECES if names[p] != 'DZ2/REG1' or p[2:4] == (-863, -1188)]
for p in new:
    others = Near(set().union(*[envs[q] for q in F.PIECES if q != p and not (
        names[p].startswith('station') and names[q].startswith('station') and abs(F.STATIONS.index(p) - F.STATIONS.index(q)) == 1
        and min(F.STATIONS.index(p), F.STATIONS.index(q)) % 2 == 0)]))
    print('%-22s %-28s pieces %3d  trace %3d  blocks %3d' % (names[p], p, others.dist(envs[p], 99), TR.dist(envs[p], 99), BL.dist(envs[p], 99)))
E = F.EATERS
allN = Near(set().union(*envs.values()))
print('eaters: pieces %d, trace %d, blocks %d' % (allN.dist(E, 99), TR.dist(E, 99), BL.dist(E, 99)))
for nm, gates in (('DEC', F.DECC), ('INC', F.INCC)):
    for i, g in enumerate(gates):
        w = wl_out((NE, -76, 7), g)
        c = (g[2] + 45, g[3] + 31)
        pth = glider_path(w, time_at(w, (c[0] - 1500, c[1] + 1500)), time_at(w, c) - 30)
        oth = Near(set().union(*[envs[q] for q in F.PIECES if q != g]))
        print('%s chain copy %d side line %s: pieces %d, blocks %d, trace %d' % (nm, i + 1, wl(w), oth.dist(pth, 99), BL.dist(pth, 99), TR.dist(pth, 99)))
    g = gates[0]
    w = wl_out((SE, 43, 5), g)
    c = (g[2] + 45, g[3] + 31)
    pth = glider_path(w, time_at(w, (c[0] - 1500, c[1] - 1500)), time_at(w, c) - 30)
    oth = Near(set().union(*[envs[q] for q in F.PIECES if q != g]))
    print('%s chain through input %s: pieces %d, blocks %d, trace %d' % (nm, wl(w), oth.dist(pth, 99), BL.dist(pth, 99), TR.dist(pth, 99)))
