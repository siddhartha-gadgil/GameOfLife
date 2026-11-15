#!/usr/bin/env python3
"""P4 (R-31): choose a random test program (seeded) for the exact runs: 3 registers, 7 instructions,
every instruction kind, one register used by >= 3 instructions (both inc and decJz, two decJz
callers, so stations j = 0 and 1 are used), every instruction executed and both decJz branches
taken on the chosen inputs, and every run halting within a step budget.
Usage: p4_random.py [SEED]   (writes results/prog_rand.json)"""
import sys
import json
import random
from lpcommon import LPRES
import os


def interpret(prog, regs, budget=40):
    regs = dict(regs)
    pc, trace, branches = 0, [], set()
    while prog[pc][0] != 'halt':
        ins = prog[pc]
        trace.append(pc)
        if len(trace) > budget:
            return None
        r = ins[1]
        if ins[0] == 'inc':
            regs[r] = regs.get(r, 0) + 1
            pc += 1
        elif regs.get(r, 0) == 0:
            branches.add((pc, 'z'))
            pc = ins[2]
        else:
            branches.add((pc, 'nz'))
            regs[r] -= 1
            pc += 1
    return regs, trace + [pc], branches


def candidate(rng, N=7, R=3):
    prog = []
    for i in range(N - 1):
        if rng.random() < 0.4:
            prog.append(('inc', rng.randrange(R)))
        else:
            prog.append(('dec', rng.randrange(R), rng.randrange(N)))
    prog.append(('halt',))
    return prog


def good(prog, inputs):
    N = len(prog)
    regs_used = {ins[1] for ins in prog if ins[0] != 'halt'}
    if regs_used != {0, 1, 2}:
        return None
    uses = {r: [ins[0] for ins in prog if ins[0] != 'halt' and ins[1] == r] for r in regs_used}
    if not any(u.count('dec') >= 2 and 'inc' in u for u in uses.values()):
        return None
    runs = []
    seen, br = set(), set()
    for inp in inputs:
        res = interpret(prog, inp)
        if res is None:
            return None
        regs, trace, b = res
        if len(trace) > 25:
            return None
        seen |= set(trace)
        br |= b
        runs.append((inp, regs, trace))
    if seen != set(range(N)):
        return None
    if br != {(i, s) for i, ins in enumerate(prog) if ins[0] == 'dec' for s in ('z', 'nz')}:
        return None
    return runs


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    inputs = [{0: 0, 1: 0, 2: 0}, {0: 1, 1: 0, 2: 0}, {0: 2, 1: 1, 2: 0}, {0: 1, 1: 2, 2: 1}]
    for trial in range(10 ** 6):
        prog = candidate(rng)
        runs = good(prog, inputs)
        if runs:
            break
    print('seed %d, trial %d: %s' % (seed, trial, prog))
    for inp, regs, trace in runs:
        print('  input %s -> %s, trace %s (%d steps)' % (inp, regs, trace, len(trace) - 1))
    json.dump({'seed': seed, 'trial': trial, 'prog': prog, 'runs': [[{str(k): v for k, v in a.items()}, {str(k): v for k, v in b.items()}, t] for a, b, t in runs]},
              open(os.path.join(LPRES, 'prog_rand.json'), 'w'))


if __name__ == '__main__':
    main()
