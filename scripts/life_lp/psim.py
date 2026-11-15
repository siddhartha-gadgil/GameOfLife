#!/usr/bin/env python3
"""psim (R-31): Python wrapper of psim.c, a sparse tiled exact Life simulator (same interface idea as
life_route/gsim.Sim, but only live tiles and their neighbours are computed).  `python3 psim.py`
cross-checks it against gsim on random soups with gliders."""
import ctypes
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
_lib = None


def lib():
    global _lib
    if _lib is None:
        d = tempfile.mkdtemp(prefix='psim_')
        so = os.path.join(d, 'psim.so')
        subprocess.check_call(['gcc', '-O3', '-march=native', '-shared', '-fPIC', '-o', so, os.path.join(HERE, 'psim.c')])
        L = ctypes.CDLL(so)
        L.sim_new.restype = ctypes.c_void_p
        L.sim_new.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_long, ctypes.c_long]
        L.sim_free.argtypes = [ctypes.c_void_p]
        P = ctypes.POINTER(ctypes.c_long)
        L.sim_set.argtypes = [ctypes.c_void_p, ctypes.c_int, P, P]
        L.sim_count.argtypes = [ctypes.c_void_p]
        L.sim_get.argtypes = [ctypes.c_void_p, P, P, P, ctypes.c_int]
        L.sim_clear.argtypes = [ctypes.c_void_p, ctypes.c_int, P, P]
        L.sim_run.argtypes = [ctypes.c_void_p, ctypes.c_long]
        _lib = L
    return _lib


class PSim:
    def __init__(self, cells, box, margin=1000):
        L = lib()
        self.L = L
        x0 = (box[0] - margin) // 64 * 64
        y0 = (box[1] - margin) // 64 * 64
        NX = (box[2] + margin - x0) // 64 + 2
        NY = (box[3] + margin - y0) // 64 + 2
        self.s = L.sim_new(NX, NY, x0, y0)
        self.set(cells)

    def _arr(self, cells):
        cells = list(cells)
        n = len(cells)
        xs = (ctypes.c_long * max(n, 1))(*[c[0] for c in cells])
        ys = (ctypes.c_long * max(n, 1))(*[c[1] for c in cells])
        return n, xs, ys

    def set(self, cells):
        n, xs, ys = self._arr(cells)
        if self.L.sim_set(self.s, n, xs, ys) != 0:
            raise ValueError('cell outside the grid')

    def clear(self, cells):
        n, xs, ys = self._arr(cells)
        self.L.sim_clear(self.s, n, xs, ys)

    def run(self, n):
        if self.L.sim_run(self.s, n) != 0:
            raise RuntimeError('pattern reached the grid border')

    def cells(self, outside=None):
        n = self.L.sim_count(self.s)
        xs = (ctypes.c_long * max(n, 1))()
        ys = (ctypes.c_long * max(n, 1))()
        b = (ctypes.c_long * 4)(*outside) if outside else None
        m = self.L.sim_get(self.s, xs, ys, b, n)
        return {(xs[i], ys[i]) for i in range(min(m, n))}

    def __del__(self):
        try:
            self.L.sim_free(self.s)
        except Exception:
            pass


if __name__ == '__main__':
    import random
    sys.path.append(os.path.join(HERE, '..', 'life_route'))
    from gsim import Sim
    random.seed(1)
    for trial in range(6):
        cells = set()
        for _ in range(8):
            cx, cy = random.randint(-300, 300), random.randint(-300, 300)
            for _ in range(60):
                cells.add((cx + random.randint(0, 12), cy + random.randint(0, 12)))
        box = (-2000, -2000, 2000, 2000)
        A = Sim(cells, box, 64)
        B = PSim(cells, box)
        for step in (1, 7, 64, 300, 1000):
            A.run(step)
            B.run(step)
            assert A.cells() == B.cells(), (trial, step)
        out = B.cells(outside=(-100, -100, 100, 100))
        assert out == {c for c in A.cells() if not (-100 <= c[0] <= 100 and -100 <= c[1] <= 100)}
        print('trial %d: %d cells after 1372 generations: psim == gsim' % (trial, len(A.cells())))
