#!/usr/bin/env python3
"""D7 (R-26): for every restore chain of results/d6_chain.txt (two harmless units), the NZ case:
the gliders of the chain with counter k (k = 0 .. 6, 40) and no detector product.  Keeps the chains
whose gliders leave counter k plus a fixed set of gliders (the same for all k)."""
import ast
from dcat import *


def parse(line):
    a = line.split('|')
    first = a[0].split(':', 1)[1]
    i = first.index('[')
    j = first.index(']', first.index('))]') if '))]' in first else 0) + 1
    g1 = ast.literal_eval(first[i:first.index('] ->') + 1])
    pos = ast.literal_eval(first[first.index('] ->') + 4:].strip())
    second = a[1].strip()
    g2 = ast.literal_eval(second[second.index('['):])
    norm = lambda L: [(tuple(w[0]), w[1], w[2]) for w in L]
    return line.split()[0], norm(g1), pos, norm(g2)


def nz_outcome(gl, ks=(0, 1, 2, 3, 4, 5, 6, 40)):
    res = None
    for k in ks:
        t0 = int(min(time_at(w, (7 + k, 11 + k)) for w in gl)) - 80
        st, t, rest, out = run_free(gl, extra=counter(k), t0=t0, max_gen=1500, max_pop=300, max_span=150)
        if st != 'settled' or set(rest) != set(counter(k)):
            return None
        if res is None:
            res = out
        elif out != res:
            return None
    return res


if __name__ == '__main__':
    seen = {}
    for line in __import__('gzip').open('results/d6_chain.txt.gz', 'rt'):
        if 'two steps' not in line:
            continue
        det, u1, pos, u2 = parse(line)
        for (name, u) in (('first', u1), ('second', u2)):
            key = tuple(sorted(u))
            if key in seen:
                continue
            seen[key] = nz_outcome(u)
    from collections import Counter
    print(Counter(len(v) if v is not None else -1 for v in seen.values()))
    for key, v in seen.items():
        if v:
            print([ (DIRNAME[w[0]], w[1], w[2]) for w in key], '->', [(DIRNAME[w[0]], w[1], w[2]) for w in v])
