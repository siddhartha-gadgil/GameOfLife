#!/usr/bin/env python3
"""P5 (R-31): the timing formulas of LP checked on many layouts (no simulation).

For random well-formed programs (various N, R, D, P) the layout is built and, for every window link,
the residue r0 (arrival at e = 0, relative to the window base of the receiving copy) is compared with
the class formula r0 = rho_0 + alpha t + beta j + gamma q (mod 30) fitted on the first layouts; the decJz
token rule is compared with the closed forms of R-31 section 4.2; the slack of the INC continue and
of the Z answer and the corner / segment gaps (check (S) of p2) are recorded.
Usage: p5_formulas.py [COUNT]   (results/p5_formulas.txt)"""
import sys
import random
from lpcommon import *
import p1_layout as P1
import p2_check as P2


def rand_prog(rng):
    while True:
        N = rng.randint(3, 9)
        R = rng.randint(1, 4)
        prog = []
        for i in range(N - 1):
            if rng.random() < 0.4:
                prog.append(('inc', rng.randrange(R)))
            else:
                prog.append(('dec', rng.randrange(R), rng.randrange(N)))
        prog.append(('halt',))
        if any(ins[0] != 'halt' for ins in prog):
            return prog


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    rng = random.Random(11)
    out = open(os.path.join(LPRES, 'p5_formulas.txt'), 'w')

    def log(s=''):
        print(s, flush=True)
        out.write(s + '\n')
    data = []
    gaps = []
    slack = {'cont': [], 'Z': []}
    tok = 0
    rt = [0, 0]
    for n in range(count):
        prog = rand_prog(rng)
        m = P1.layout(prog)
        D = m.D
        for L in m.links:
            if 'r0' in L and L['kind'] != 'C':
                j = L.get('j', 0)
                data.append((L['kind'], L.get('t', 0), j, D, m.P, L['r0'], L['e']))
            if L['kind'] == 'C':
                q = D - 1 - L['j']
                data.append(('C', 2 * L['j'], L['j'], D, m.P, L['r0'], L['eC']))
                eC = (9 * q) % 15
                dN0 = -3936 - 228 * q
                dZ0 = 367 + 1564 * q - 8 * eC
                sg = 2 * (q % 2)
                x = max(0, -(-(dZ0 - 30 * sg + 1) // 120))
                want = (eC, dN0, dZ0, sg, x, (-1 - dZ0 + 30 * sg + 120 * x) // 8, (-dN0 - 2 * sg) // 8)
                got = (L['eC'], L['dN0'], L['dZ0'], L['sigma'], L['x'], m.byname[L['name'][:-1] + 'KZ']['e'],
                       m.byname[L['name'][:-1] + 'KNZ']['e'])
                assert got == want, (prog, L['name'], got, want)
                tok += 1
            if L['kind'] in slack:
                slack[L['kind']].append(L['slack'])
        # route time formula: T(last corner) = T(first corner) + 2 (Manhattan length in (u, v)) - 5 (turns - 1)
        for L in m.links:
            cs, lg = L['corners'], L['legs']
            if len(cs) < 2:
                continue
            t0 = tuv(lg[1], *cs[0])
            pred = t0 + sum(2 * (abs(cs[k][0] - cs[k - 1][0]) + abs(cs[k][1] - cs[k - 1][1])) for k in range(1, len(cs))) - 5 * (len(cs) - 1)
            got = tuv(lg[-1], *cs[-1])
            rt[0] += 1
            if pred != got:
                rt[1] += 1
                log('  route time formula FAIL %s: %s vs %s' % (L['name'], pred, got))
        # (S) gaps
        segs = [(L['name'], s) for L in m.links for s in P2.segments(m, L)]
        g = 10 ** 9
        for L in m.links:
            for idx, (cu, cv) in enumerate(L['corners']):
                for ln, (k, gg, typ, cc, lo, hi) in segs:
                    if ln == L['name'] and k in (idx, idx + 1):
                        continue
                    if typ == 'u' and lo - 30 <= cv <= hi + 30:
                        g = min(g, abs(cu - cc))
                    if typ == 'v' and lo - 30 <= cu <= hi + 30:
                        g = min(g, abs(cv - cc))
        gaps.append(g)
        log('program %2d N %d R %d D %d P %d: %s; min corner/segment gap %d; pieces %d' % (n, m.N, m.R, D, m.P, prog, g, len(m.pieces)))
    # fit r0 = rho0 + alpha t + beta j (mod 30) per class
    log('\nresidue r0 of the window links (arrival for e = 0, relative to the window base tau_t of the receiving copy):')
    classes = sorted({d[0] for d in data})
    for cl in classes:
        rows = [d for d in data if d[0] == cl]
        sol = None
        for a in range(30):
            for b in range(30):
                for c in range(30):
                    rho = {(rw[5] - a * rw[1] - b * rw[2] - c * (rw[3] - 1 - rw[2])) % 30 for rw in rows}
                    if len(rho) == 1:
                        sol = (rho.pop(), a, b, c)
                        break
                if sol:
                    break
            if sol:
                break
        ts = sorted({rw[1] for rw in rows})
        js = sorted({rw[2] for rw in rows})
        log('  %-6s %4d links (copies t %s, j %s): r0 = %s' % (cl, len(rows), ts, js,
            ('%d + %d t + %d j + %d q (mod 30), q = D - 1 - j' % sol) if sol else 'NO AFFINE FIT'))
    log('\ndecJz token rule (section 4.2) matched the closed forms for %d decJz instructions' % tok)
    log('INC continue slack (generations): min %d over %d; Z answer slack: min %d over %d' % (
        min(slack['cont']) if slack['cont'] else 0, len(slack['cont']), min(slack['Z']) if slack['Z'] else 0, len(slack['Z'])))
    log('route time = 2 x (Manhattan (u, v) length between first and last corner) - 5 x (turns): checked on %d links, %d failures' % tuple(rt))
    log('corner / foreign-segment gap: min %d over %d layouts (>= 60 required)' % (min(gaps), len(gaps)))


if __name__ == '__main__':
    main()
