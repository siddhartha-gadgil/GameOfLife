#!/usr/bin/env python3
"""P3 (R-31): exact simulation (psim, sparse tiled, unbounded plane; escaping gliders removed only
when outside the core box and moving away) of LP(program) from the start glider to halting.

Checks: exactly one escaped glider, on the HALT line, and it passes the HALT cell; after it has left,
30 000 more generations; then the whole plane equals, cell by cell, the cycle of all pieces + eaters
+ register blocks at the interpreter's final values.  Also records the start time of every
instruction activation (the time the entry-copy gate of the unit is passed), for the report.
Usage: p3_run.py PROGRAM r0=a,r1=b,...   (results/p3_<program>_<inputs>.txt)"""
import sys
import time
from lpcommon import *
import p1_layout as P1
from psim import PSim
from common import components, glider_worldline


def interpret(prog, regs):
    regs = dict(regs)
    pc, trace = 0, []
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
        if len(trace) > 10 ** 5:
            raise RuntimeError('no halt')
    return regs, trace + [pc]


def main():
    name = sys.argv[1]
    vals = {}
    if len(sys.argv) > 2 and sys.argv[2]:
        for a in sys.argv[2].split(','):
            k, v = a.split('=')
            vals[int(k[1:])] = int(v)
    prog = [tuple(x) for x in P1.get_prog(name)]
    m = P1.layout(prog)
    final, trace = interpret(prog, vals)
    for r in range(m.R):
        vals.setdefault(r, 0)
        final.setdefault(r, 0)
    tag = '_'.join('r%d=%d' % (r, vals[r]) for r in range(m.R))
    out = open(os.path.join(LPRES, 'p3_%s_%s.txt' % (name, tag)), 'w')

    def log(s):
        print(s, flush=True)
        out.write(s + '\n')
        out.flush()

    log('program %s = %s; input %s; interpreter: final %s, instruction trace %s' % (name, prog, vals, final, trace))
    log('layout LP: %d pieces, %d eater cells; start %s at t = %d; halt line %s; HALT cell (u, v) %s' % (
        len(m.pieces), len(m.eaters), wl(m.start), m.start_t, wl(m.halt), m.halt_cell_uv))
    t0 = m.start_t - 60
    cells = state(m.pieces, [m.start], t0, set(m.eaters) | P1.blocks_of(m, vals))
    eb = bbox(m.eaters)
    cbox = core_box(m.pieces, [eb], margin=80)
    log('core box %s (%d x %d)' % (cbox, cbox[2] - cbox[0], cbox[3] - cbox[1]))
    S = PSim(cells, cbox, margin=3000)
    t = t0
    removed = []
    chunk = 600
    t_halt = None
    hu, hv = m.halt_cell_uv
    hcell = xy(hu, hv)
    T0 = time.time()
    tmax = int(os.environ.get('P3_TMAX', '20000000'))
    while t < tmax:
        S.run(chunk)
        t += chunk
        out_c = S.cells(outside=cbox)
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
                away = (bb[0] > cbox[2] and w[0][0] > 0) or (bb[2] < cbox[0] and w[0][0] < 0) or \
                       (bb[1] > cbox[3] and w[0][1] > 0) or (bb[3] < cbox[1] and w[0][1] < 0)
                if away:
                    removed.append(w)
                    drop |= comp
                    on_halt = w[:2] == m.halt[:2]
                    log('  t = %d: glider %s left the machine%s' % (t, wl(w), ' (HALT line)' if on_halt else ''))
                    if on_halt and t_halt is None:
                        t_halt = t
                        # the HALT cell is on the line and visited by the glider (time of passage)
                        log('     passes the HALT cell %s at t = %.0f' % (hcell, time_at(w, hcell)))
            if drop:
                S.clear(drop)
        if t % 60000 < chunk:
            log('  t = %d (%.0f s)' % (t, time.time() - T0))
        if t_halt is not None and t >= t_halt + 30000:
            break
    want = state(m.pieces, [], t, set(m.eaters) | P1.blocks_of(m, final))
    cs = S.cells()
    ok = cs == want and len(removed) == 1 and removed[0][:2] == m.halt[:2]
    log('halted: escaped gliders %s; halt glider left the core box at t = %d (start t = %d): %d generations' % (
        [wl(w) for w in removed], t_halt if t_halt else -1, m.start_t, (t_halt - m.start_t) if t_halt else -1))
    log('end t = %d: state == cycle of all pieces + eaters + blocks %s: %s%s  (%.0f s)' % (
        t, final, 'ok' if ok else 'FAIL', '' if ok else ' (extra %d cells %s, missing %d %s)' % (
            len(cs - want), bbox(cs - want) if cs - want else None, len(want - cs), bbox(want - cs) if want - cs else None),
        time.time() - T0))


if __name__ == '__main__':
    main()
