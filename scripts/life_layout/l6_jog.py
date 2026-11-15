#!/usr/bin/env python3
"""L6 (R-30): the hairpin with one jog (used by the layout rule only as a fallback for token timing),
checked in isolation by exact simulation: an SE glider through the turns
(SW, h), (SE, H), (SW, h + 50), (SE, H - 60), (NE, h + 100), for all 4 combinations of lane parities;
the predicted final world line (net.reflect) must be the only glider left and the reflectors back in
their cycle; also the arrival shift +230 against the plain hairpin."""
from lcommon import *
import l2_layout as L2

out = open(os.path.join(RES, 'l6_jog.txt'), 'w')
for (u0, tau) in ((0, 0), (1, 0), (0, 1), (1, 3)):
    g = (SE, u0, 1000 + tau)
    h, H = 400, -300
    turns = [(SW, h), (SE, H), (SW, h + 50), (SE, H - L2.JOG_W), (NE, h + 100), (SE, 300)]
    pcs, gf, cor, legs = L2.route(g, turns)
    plain, gp, _, _ = L2.route(g, [(SW, h), (SE, H), (NE, h + 100), (SE, 300)])
    envs = [env_cells(p) for p in pcs]
    dmin = min(set_dist(envs[i], envs[j]) for i in range(len(envs)) for j in range(i))
    t0 = 30 * (int(time_at(g, xy(*cor[0]) if (cor[0][0] + cor[0][1]) % 2 == 0 else (0, 0))) // 30) - 600
    t1 = t0 + 30 * 400
    cells, rem = run_peel(pcs, [g], t0, t1, cbox=core_box(pcs, margin=60))
    ok = cells == state(pcs, [], t1) and rem == [gf]
    s = 'start %s: corners %s; final %s (plain hairpin %s, shift %d); min envelope distance %d; exact run: %s' % (
        wl(g), cor, wl(gf), wl(gp), gf[2] - gp[2], dmin, 'ok' if ok else 'FAIL %s' % rem)
    print(s)
    out.write(s + '\n')
