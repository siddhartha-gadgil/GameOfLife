#!/usr/bin/env python3
"""L4 (R-30): exact simulation (gsim, unbounded plane, escaping gliders peeled off only when provably
gone) of the whole machine of a program, from the start glider to halting.

Check: the run ends with exactly one escaped glider, on the HALT line; after the halt glider has
left, the run is continued until every register has finished (30 000 generations), and the final
state must equal, cell by cell, the cycle of all pieces + the eaters + the register blocks at the
values computed by the counter-machine interpreter.
Usage: l4_run.py PROGRAM r0=a,r1=b,...   (results/l4_<program>_<inputs>.txt)"""
import sys
import time
from lcommon import *
import l2_layout as L2
from l3_check import PROGS
from gsim import Sim
from common import components, glider_worldline


def interpret(prog, regs):
    regs = dict(regs)
    pc, steps, trace = 0, 0, []
    while prog[pc][0] != 'halt':
        ins = prog[pc]
        trace.append(pc)
        r = ins[1]
        if ins[0] == 'inc':
            regs[r] = regs.get(r, 0) + 1
            pc += 1
        elif regs.get(r, 0) == 0:
            pc = ins[2]
        else:
            regs[r] -= 1
            pc += 1
        steps += 1
    return regs, trace + [pc]


def main():
    name = sys.argv[1]
    vals = {}
    if len(sys.argv) > 2 and sys.argv[2]:
        for a in sys.argv[2].split(','):
            k, v = a.split('=')
            vals[int(k[1:])] = int(v)
    prog = PROGS[name]
    m = L2.layout(prog)
    final, trace = interpret(prog, vals)
    for r in m.regs:
        vals.setdefault(r, 0)
        final.setdefault(r, 0)
    out = open(os.path.join(RES, 'l4_%s_%s.txt' % (name, '_'.join('r%d=%d' % (r, vals[r]) for r in m.regs))), 'w')

    def log(s):
        print(s, flush=True)
        out.write(s + '\n')
        out.flush()

    log('program %s = %s; input %s; interpreter: final %s, instruction trace %s' % (name, prog, vals, final, trace))
    log('layout: %d pieces, %d eater cells; start %s; halt line %s' % (len(m.pieces), len(m.eaters), wl(m.start), wl(m.halt)))
    t0 = m.start_t - 60
    init = L2.blocks_of(m, vals)
    cells = state(m.pieces, [m.start], t0, set(m.eaters) | init)
    eb = bbox(m.eaters)
    cbox = core_box(m.pieces, [eb], margin=80)
    gbox = (cbox[0] - 300, cbox[1] - 300, cbox[2] + 300, cbox[3] + 300)
    log('core box %s (%d x %d)' % (cbox, cbox[2] - cbox[0], cbox[3] - cbox[1]))
    S = Sim(cells, gbox, 64)
    t = t0
    removed = []
    chunk = 600
    t_halt = None
    T0 = time.time()
    tmax = int(os.environ.get('L4_TMAX', '3000000'))
    while t < tmax:
        S.run(chunk)
        t += chunk
        cs = S.cells()
        out_c = [x for x in cs if not (cbox[0] <= x[0] <= cbox[2] and cbox[1] <= x[1] <= cbox[3])]
        if out_c:
            drop = set()
            for comp in components(set(out_c), 2):
                w = glider_worldline(comp, t)
                bb = bbox(comp)
                if w is None:
                    log('  t = %d: non-glider object outside the core box at %s' % (t, bb))
                    raise SystemExit(1)
                if min(abs(bb[0] - cbox[0]), abs(bb[2] - cbox[2]), abs(bb[1] - cbox[1]), abs(bb[3] - cbox[3])) < 10:
                    continue
                # moving away from the box?
                away = (bb[0] > cbox[2] and w[0][0] > 0) or (bb[2] < cbox[0] and w[0][0] < 0) or \
                       (bb[1] > cbox[3] and w[0][1] > 0) or (bb[3] < cbox[1] and w[0][1] < 0)
                if away:
                    removed.append(w)
                    drop |= comp
                    log('  t = %d: glider %s left the machine' % (t, wl(w)))
                    if w[:2] == m.halt[:2] and t_halt is None:
                        t_halt = t
            if drop:
                S.set(cs - drop)
        if t % 30000 < chunk:
            log('  t = %d (%.0f s)' % (t, time.time() - T0))
        if t_halt is not None and t >= t_halt + 30000:
            break
    want = state(m.pieces, [], t, set(m.eaters) | L2.blocks_of(m, final))
    cs = S.cells()
    ok = cs == want and len(removed) == 1 and removed[0][:2] == m.halt[:2]
    log('halted: halt glider %s left at t = %d (start t = %d): %d generations' % (
        [wl(w) for w in removed], t_halt if t_halt else -1, m.start_t, (t_halt - m.start_t) if t_halt else -1))
    log('end t = %d: state == cycle of all pieces + eaters + blocks %s: %s%s' % (
        t, final, 'ok' if ok else 'FAIL', '' if ok else ' (extra %d cells %s, missing %d)' % (
            len(cs - want), bbox(cs - want) if cs - want else None, len(want - cs))))


if __name__ == '__main__':
    main()
