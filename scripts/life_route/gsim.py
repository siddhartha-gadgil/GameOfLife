#!/usr/bin/env python3
"""gsim (R-29): Python wrapper of gsim.c (compiled on first use into a temporary directory).

Sim(cells, box): a bit-packed grid around `box` (+ margin); `run(n)` evolves n generations and
raises if a live cell ever comes within 64 cells of the grid border, so every run is exact for the
unbounded plane.  `python3 gsim.py` cross-checks it against the set simulator of life_gates."""
import ctypes
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
for sub in ('life_machine', 'life_zero', 'life_gates'):
    p = os.path.join(HERE, '..', sub)
    if p not in sys.path:
        sys.path.append(p)

_lib = None


def lib():
    global _lib
    if _lib is None:
        d = tempfile.mkdtemp(prefix='gsim_')
        so = os.path.join(d, 'gsim.so')
        subprocess.check_call(['gcc', '-O3', '-march=native', '-shared', '-fPIC', '-o', so, os.path.join(HERE, 'gsim.c')])
        L = ctypes.CDLL(so)
        L.sim_new.restype = ctypes.c_void_p
        L.sim_new.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_long, ctypes.c_long]
        L.sim_free.argtypes = [ctypes.c_void_p]
        L.sim_set.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.POINTER(ctypes.c_long), ctypes.POINTER(ctypes.c_long)]
        L.sim_count.argtypes = [ctypes.c_void_p]
        L.sim_get.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_long), ctypes.POINTER(ctypes.c_long)]
        L.sim_run.argtypes = [ctypes.c_void_p, ctypes.c_long, ctypes.POINTER(ctypes.c_long)]
        L.sim_box.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_long)]
        _lib = L
    return _lib


class Sim:
    def __init__(self, cells, box, margin=200):
        """box = (xmin, ymin, xmax, ymax) of the region the pattern may visit."""
        L = lib()
        x0 = box[0] - margin - 128
        y0 = box[1] - margin
        W = (box[2] - box[0] + 2 * margin + 256) // 64 + 2
        H = box[3] - box[1] + 2 * margin
        self.L = L
        self.s = L.sim_new(W, H, x0, y0)
        self.box = (ctypes.c_long * 4)(10 ** 9, 10 ** 9, -10 ** 9, -10 ** 9)
        self.set(cells)

    def set(self, cells):
        cells = list(cells)
        n = len(cells)
        xs = (ctypes.c_long * max(n, 1))(*[c[0] for c in cells])
        ys = (ctypes.c_long * max(n, 1))(*[c[1] for c in cells])
        if self.L.sim_set(self.s, n, xs, ys) != 0:
            raise ValueError('cell outside the grid')

    def run(self, n):
        if self.L.sim_run(self.s, n, self.box) != 0:
            raise RuntimeError('pattern reached the grid border')

    def cells(self):
        n = self.L.sim_count(self.s)
        xs = (ctypes.c_long * max(n, 1))()
        ys = (ctypes.c_long * max(n, 1))()
        m = self.L.sim_get(self.s, xs, ys)
        return {(xs[i], ys[i]) for i in range(m)}

    def runbox(self):
        return tuple(self.box)

    def __del__(self):
        try:
            self.L.sim_free(self.s)
        except Exception:
            pass


def selftest():
    import random
    from common import step_cells, glider_at, SE, NW
    random.seed(1)
    for trial in range(6):
        c = {(random.randrange(-40, 40), random.randrange(-30, 30)) for _ in range(900)}
        c |= glider_at(SE, 3 * trial, 0, 0) | glider_at(NW, 50 + trial, 0, 0)
        S = Sim(c, (-200, -200, 200, 200), margin=100)
        ref = set(c)
        for g in range(1, 301):
            ref = step_cells(ref)
            if g in (1, 2, 7, 64, 300):
                S2 = Sim(c, (-200, -200, 200, 200), margin=100)
                S2.run(g)
                assert S2.cells() == ref, (trial, g)
        S.run(300)
        assert S.cells() == ref
    # border detection
    S = Sim(glider_at(SE, 0, 0, 0), (0, 0, 10, 10), margin=10)
    try:
        S.run(4000)
        raise AssertionError('border not detected')
    except RuntimeError:
        pass
    print('gsim: agrees with the set simulator (6 random soups + 2 gliders, 300 generations); border check works')


if __name__ == '__main__':
    selftest()
