#!/usr/bin/env python3
"""D3 (R-26): single-glider block moves and sequences of them from counter (-1) to counter 0 in
which every glider passes all blocks counter k, k >= 0 (so the sequence is harmless when the
register is not at -1).

Catalogue: block at (0, 0), one glider of direction d on lane l (lane relative to the block),
outcome a single block displaced by (u, v) and nothing else.
"""
import os
import sys
from collections import deque
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
from common import SE, SW, NE, NW, counter, glider_at, DIRNAME, cells_of_window, translate   # noqa: E402
from reactions import run_free                                                              # noqa: E402
from net import time_at                                                                     # noqa: E402

BLOCK = frozenset(cells_of_window(0, 0, [3, 3]))


def outcome(d, lane, block_at=(0, 0)):
    wl = (d, lane, 0)
    b = translate(BLOCK, *block_at)
    st, t, rest, gl = run_free([wl], extra=b, t0=int(time_at(wl, block_at)) - 60, max_gen=800,
                               max_pop=300, max_span=150)
    return st, rest, gl


def catalogue():
    moves = []
    passing = {}
    for d in (SE, SW, NW, NE):
        for lane in range(-20, 21):
            st, rest, gl = outcome(d, lane)
            if st == 'settled' and gl == [(d, lane, 0)] and set(rest) == set(BLOCK):
                passing.setdefault(d, set()).add(lane)
                continue
            if st == 'settled' and not gl and len(rest) == 4:
                xs = sorted(rest)
                u, v = xs[0]
                if set(translate(BLOCK, u, v)) == set(rest):
                    moves.append((d, lane, (u, v)))
    return moves, passing


def lane_of(d, p):
    return d[1] * p[0] - d[0] * p[1]


if __name__ == '__main__':
    moves, passing = catalogue()
    for m in moves:
        print('move', DIRNAME[m[0]], 'rel lane', m[1], 'displacement', m[2])
    inter = {d: [l for l in range(-20, 21) if l not in passing[d]] for d in passing}
    for d in inter:
        print('interacting rel lanes', DIRNAME[d], min(inter[d]), '..', max(inter[d]))

    def harmless(d, L):
        """the absolute lane L passes every counter k, k >= 0 (block (7 + k, 11 + k))"""
        for k in range(0, 60):
            rel = L - lane_of(d, (7 + k, 11 + k))
            if rel in inter[d]:
                return False
        return True

    start = (6, 10)
    goal = (7, 11)
    # BFS over block positions; first move must be a detector (glider harmless for k >= 0)
    prev = {start: None}
    dq = deque([start])
    while dq:
        p = dq.popleft()
        if p == goal:
            break
        for (d, rl, (u, v)) in moves:
            L = rl + lane_of(d, p)
            if not harmless(d, L):
                continue
            q = (p[0] + u, p[1] + v)
            if abs(q[0] - 7) > 12 or abs(q[1] - 11) > 12 or q in prev:
                continue
            prev[q] = (p, d, L)
            dq.append(q)
    seq = []
    q = goal
    while prev.get(q):
        p, d, L = prev[q]
        seq.append((p, DIRNAME[d], L, q))
        q = p
    print('shortest sequence from counter(-1) to counter 0 by harmless gliders:')
    for s in reversed(seq):
        print('  block', s[0], 'glider', s[1], 'lane', s[2], '-> block', s[3])
    # all positions reachable, with distances
    print('reachable positions:', len(prev))
