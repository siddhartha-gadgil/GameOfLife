#!/usr/bin/env python3
"""Lean emitter for a run with a register block at every position k >= K0 (untrusted generator).

Input: a segment plan of the run WITHOUT the block (plan.py, DZ2_K=nb).  The block enters as
generic processes: before the salvo is free, the block `reg1Block k` (a still life); from then on
the salvo and the block together, `PullX k = translate (148, 240) (PullS ∪ counter k)`, a
trajectory with the footprint `PullG k i` of `salvo_world_all`.  After the planned run a tail of
4 k generations lets the salvo finish for every k.

Usage: emit_generic.py PLAN.pkl PREFIX MODULEDIR K0 [SEGS_PER_FILE]"""
import os
import pickle
import sys
from emit import (Emitter, HEADER, FOOTER, z, ofrows, ofrows_ml, box, evolve, window_of_cells)

VX, VY = 148, 240
BAND = (-110, -80)          # SE lanes u = x - y of the salvo


def is_salvo(p):
    return p['kind'] == 'flight' and p['v'] == (1, 1) and \
        all(BAND[0] <= x - y <= BAND[1] for x, y in p['start'])


class GenEmitter(Emitter):
    def __init__(self, plan, prefix, K0, d=-1):
        super().__init__(plan, prefix)
        self.K0 = K0
        self.d = d
        segs = plan['segs']
        def scount(sg):
            return sum(len(p['start']) for p in sg['procs'] if is_salvo(p))
        full = scount(segs[-1])
        self.js = min(j for j, sg in enumerate(segs) if scount(sg) == full and
                      all(scount(s2) == full for s2 in segs[j:]))
        self.ts = segs[self.js]['a']
        for sg in segs[self.js:]:
            assert any(is_salvo(p) for p in sg['procs']), 'the salvo must stay free to the end'
        sal = set()
        for p in segs[self.js]['procs']:
            if is_salvo(p):
                sal |= set(p['start'])
        self.salvo_w = sal
        self.salvo_l = {(x - VX, y - VY) for x, y in sal}

    # ------------------------------------------------------------ the generic salvo process
    def pull_lemmas(self):
        P = self.P
        S = self.salvo_l
        c = set(S)
        pb = None
        for _ in range(4):
            b = window_bbox(c)
            pb = b if pb is None else (min(pb[0], b[0]), min(pb[1], b[1]), max(pb[2], b[2]), max(pb[3], b[3]))
            c = evolve(c, 1)
        assert pb[3] <= 9, 'the salvo must stay above row 9'
        # move the salvo forward along its diagonal, right up to the block: the long approach is
        # covered by the moving box, the certificate only by the collision
        c0 = 9 - pb[3]
        self.c0 = c0
        S = {(x + c0, y + c0) for x, y in S}
        self.salvo_l = S
        self.vx, self.vy = VX - c0, VY - c0
        pb = (pb[0] + c0, pb[1] + c0, pb[2] + c0, pb[3] + c0)
        blk0 = {(7, 11), (8, 11), (7, 12), (8, 12)}
        dd = self.d
        tgt = {(7 + dd, 11 + dd), (8 + dd, 11 + dd), (7 + dd, 12 + dd), (8 + dd, 12 + dd)}
        c = set(S) | blk0
        zb = window_bbox(c)
        n0 = 0
        while c != tgt:
            c = evolve(c, 1)
            n0 += 1
            assert n0 < 3000, 'the salvo does not pull the block'
            if c:
                b = window_bbox(c)
                zb = (min(zb[0], b[0]), min(zb[1], b[1]), max(zb[2], b[2]), max(zb[3], b[3]))
        self.n0 = n0
        self.pb, self.zb = pb, zb
        Sx, Sy, Srows = window_of_cells(S)
        U = S | blk0
        Zx, Zy, _ = window_of_cells(U)
        out = []
        out.append('/-- The pulling salvo in the frame of `counter` (generated). -/\ndef %sPullS : Finset Cell :=\n  %s\n'
                   % (P, ofrows(S)))
        out.append('/-- The salvo moves one cell down and to the right every four generations. -/\n'
                   'theorem %sPullS_four : conway.evolve 4 %sPullS = translate (1, 1) %sPullS := by\n'
                   '  rw [%sPullS, translate_ofRows]\n  life_cert\n' % (P, P, P, P))
        out.append('/-- The salvo during its first four generations. -/\n'
                   'theorem %sPullS_box : ∀ r < 4, (conway.evolve r %sPullS : Set Cell) ⊆ %s := by\n'
                   '  intro r hr\n  interval_cases r <;> (rw [%sPullS]; life_eval; exact coe_ofRows_subset_box rfl)\n'
                   % (P, P, box(pb), P))
        out.append('set_option maxRecDepth 100000 in\n/-- **Certificate**: the salvo pulls the block at position `0` to `-1`. -/\n'
                   'theorem %sPullHz :\n    Reaction (%sPullS ∪ counter 0) (counter (%d)) %d (fun _ => %s) := by\n'
                   '  rw [show %sPullS ∪ counter 0 = %s by\n'
                   "      rw [%sPullS, counter, ofRows_eq_padRows' %s %s %s %s %d %d _ (by norm_num) (by norm_num),\n"
                   "        ofRows_eq_padRows' %s %s (7 + 0) (11 + 0) %d %d _ (by norm_num) (by norm_num),\n"
                   '        ← ofRows_orRows]\n      rfl,\n'
                   '    show counter (%d) = ofRows %d %d [3, 3] by rw [counter]; norm_num]\n  life_reaction\n'
                   % (P, P, self.d, n0, box(zb), P, ofrows(U), P, z(Zx), z(Zy), z(Sx), z(Sy), Sy - Zy, Sx - Zx,
                      z(Zx), z(Zy), 11 - Zy, 7 - Zx, self.d, 7 + self.d, 11 + self.d))
        out.append('/-- The salvo and the register block at position `k`, placed at the register. -/\n'
                   'def %sPullX (k : ℕ) : Finset Cell :=\n  translate (%d, %d) (%sPullS ∪ counter ((k + %d : ℕ) : ℤ))\n'
                   % (P, self.vx, self.vy, P, c0))
        out.append('/-- The footprint of the salvo and the block at generation `i`. -/\n'
                   'def %sPullG (k i : ℕ) : Set Cell := %s\n' % (P, self.pullg('k', 'i')))
        out.append('/-- Every generation of the salvo and the block lies in its footprint. -/\n'
                   'theorem %sPullAll (k i : ℕ) : (conway.evolve i (%sPullX k) : Set Cell) ⊆ %sPullG k i :=\n'
                   '  salvo_world_all %sPullS_four %sPullS_box %sPullHz (by norm_num) %d %d (k + %d) i\n'
                   % (P, P, P, P, P, P, self.vx, self.vy, c0))
        return out

    def pullg(self, k, i):
        a, lo, b, hi = self.pb[0], self.pb[1], self.pb[2], self.pb[3]
        za, zlo, zb, zhi = self.zb
        VXc, VYc = self.vx, self.vy
        q = '((%s / 4 : ℕ) : ℤ)' % i
        kk = '(%s + %d)' % (k, self.c0)
        K = '((%s + %d : ℕ) : ℤ)' % (k, self.c0)
        D = z(self.d)
        return ('if %s ≤ %s * 4 then Box (%s + %d + %s) (%s + %d + %s) (%s + %d + %s) (%s + %d + %s) ∪ '
                'Box (7 + %d + %s) (8 + %d + %s) (11 + %d + %s) (12 + %d + %s) else if %s ≤ %s * 4 + %d then '
                'Box (%s + %d + %s) (%s + %d + %s) (%s + %d + %s) (%s + %d + %s) else '
                'Box (7 + %s + %d + %s) (8 + %s + %d + %s) (11 + %s + %d + %s) (12 + %s + %d + %s)'
                % (i, kk, z(a), VXc, q, z(b), VXc, q, z(lo), VYc, q, z(hi), VYc, q,
                   VXc, K, VXc, K, VYc, K, VYc, K, i, kk, self.n0,
                   z(za), VXc, K, z(zb), VXc, K, z(zlo), VYc, K, z(zhi), VYc, K,
                   D, VXc, K, D, VXc, K, D, VYc, K, D, VYc, K))

    # ------------------------------------------------------------ separation with a generic process
    def gfar(self, gfp, other):
        """`FarApart 2 (generic footprint) (other)` for all i < n (inside `fun i _hi => ...`)."""
        if gfp == 'block':
            return '(Box.farApart (by omega) : FarApart 2 (%s) (%s))' % (self.blockbox(), other)
        m = gfp
        return ('(farApart_ite3_left (fun _hc => Box.farApart (by omega)) (fun _hc => Box.farApart (by omega))\n'
                '          (fun _hc _hc\' => Box.farApart (by omega)) (fun _hc _hc\' => Box.farApart (by omega)) :\n'
                '          FarApart 2 (%sPullG k (i + %d)) (%s))'
                % (self.P, m, other))

    def blockbox(self):
        return 'Box (155 + (k : ℤ)) (156 + (k : ℤ)) (251 + (k : ℤ)) (252 + (k : ℤ))'

    # ------------------------------------------------------------ segments
    def segment(self, j, seg, n_sym=None):
        P = self.P
        Ts = self.plan['Ts']
        a, b = seg['a'], seg['b']
        n = b - a
        s, s2 = (a - Ts) % 30, (b - Ts) % 30
        movers = [p for p in seg['procs'] if p['kind'] in ('cert', 'flight', 'still') and p['start']
                  and not (j >= self.js and is_salvo(p))]
        idle = sorted(self.gi[p['group']] for p in seg['procs'] if p['kind'] == 'idle')
        lits = [self.mover(j, m, p, n) for m, p in enumerate(movers)]
        if j < self.js:
            gfp = 'block'
            glit = ('{ P := reg1Block (k : ℤ), Q := reg1Block (k : ℤ), F := fun _ => %s,\n'
                    '     reaction := ((counter_isStillLife (k : ℤ)).translate _).reaction_box\n'
                    '       (reg1Block_subset_box (k : ℤ)) %d }' % (self.blockbox(), n))
            gstart = gstop = 'reg1Block ↑k'
        else:
            m = a - self.ts
            gfp = m
            glit = ('{ P := conway.evolve %d (%sPullX k), Q := conway.evolve %d (%sPullX k),\n'
                    '     F := fun i => %sPullG k (i + %d),\n'
                    '     reaction := trajectory_reaction\' (%sPullAll k) %d %d %d (by norm_num) }'
                    % (m, P, m + n, P, P, m, P, m, n, m + n))
            gstart = 'conway.evolve %d (%sPullX k)' % (m, P)
            gstop = 'conway.evolve %d (%sPullX k)' % (m + n, P)
        keep = set(idle)
        sub = 'List.Sublist.slnil'
        for i in reversed(range(len(self.pg))):
            sub = '(List.Sublist.%s _ %s)' % ('cons_cons' if i in keep else 'cons', sub)
        lst = '[' + ', '.join('%sG%d' % (P, i) for i in idle) + ']'
        self.seglem.append('/-- Phase bookkeeping (segment %d). -/\ntheorem %sH%d : (%d + %d) %% 30 = %d := by norm_num\n'
                           % (j, P, j, n, s, s2))
        self.seglem.append('/-- The idle groups of segment %d are pairwise far apart. -/\n'
                           'theorem %sSub%d : (%s : List Piece).Pairwise Piece.Sep :=\n  List.Pairwise.sublist\n    %s\n    %sPieces_sep\n'
                           % (j, P, j, lst, sub, P))
        bundle = 'Piece.bundle %s %sSub%d %d %d %d %sH%d' % (lst, P, j, s, n, s2, P, j)
        self.seglem.append('/-- The processes of segment %d (generations %d to %d of the run), block at `k`. -/\n'
                           'def %sL%d (k : ℕ) : List (Proc %d) :=\n  [%s]\n'
                           % (j, a, b, P, j, n, ',\n   '.join([glit] + lits + [bundle])))
        # the generic process first
        gterms = ['(fun i _hi => %s)' % self.gfar(gfp, self.fp(q, 'i')) for q in movers]
        bterms = ['(fun i _hi => %s)' % self.gfar(gfp, box(self.pg[gi][2])) for gi in idle]
        gb = ('Piece.indep_bundle _ _ _ _ _ _\n        ⟨' + ',\n         '.join(bterms + ['trivial']) + '⟩'
              if bterms else 'Piece.indep_bundle _ _ _ _ _ _ trivial')
        parts = ['⟨' + ',\n      '.join(gterms + [gb, 'trivial']) + '⟩']
        for x, p in enumerate(movers):
            terms = [self.indep(p, q) for q in movers[x + 1:]] + [self.indep_bundle(p, idle)]
            parts.append('⟨' + ',\n      '.join(terms + ['trivial']) + '⟩')
        parts.append('trivial')
        self.seglem.append('set_option maxRecDepth 100000 in\n/-- **Segment %d** of the run, block at `k`. -/\n'
                           'theorem %sSeg%d (k : ℕ) (_hk : %d ≤ k) :\n'
                           '    Reaction (Proc.start (%sL%d k)) (Proc.stop (%sL%d k)) %d (Proc.foot (%sL%d k)) :=\n'
                           '  Reaction.parList _ (PairR.pairwise\n    %s)\n'
                           % (j, P, j, self.K0, P, j, P, j, n, P, j, self.nest(parts, '    ')))
        start = [(gstart, None)] + [(self.atom(p['start']), set(p['start'])) for p in movers]
        start += [('conway.evolve %d %sR%d' % (s, P, i), self.rest_cells(i, a)) for i in idle]
        stop = [(gstop, None)] + [(self.atom(p['stop'] if p['kind'] != 'still' else p['start']),
                                   set(p['stop'] if p['kind'] != 'still' else p['start'])) for p in movers]
        stop += [('conway.evolve %d %sR%d' % (s2, P, i), self.rest_cells(i, b)) for i in idle]
        if j == self.js:
            # the salvo atoms of the previous segment join the block
            pass
        return start, stop

    # ------------------------------------------------------------ glue
    def glue(self, j, stop, start):
        P = self.P
        A, B = list(stop), list(start)
        special = None
        if j + 1 == self.js:
            # the start of the salvo process is the concrete salvo and the block
            sa = self.atom(self.salvo_w)
            B.remove(('conway.evolve 0 (%sPullX k)' % P, None))
            B.append((sa, set(self.salvo_w)))
            B.append(('reg1Block ↑k', None))
            name = '%sZ%d_pull' % (P, j)
            self.gluelem.append(
                '/-- Glue %d: the salvo and the block become one process. -/\n'
                'theorem %s (k : ℕ) : %s ∪ reg1Block ↑k = conway.evolve 0 (%sPullX k) := by\n'
                '  rw [Rule.evolve_zero, %sPullX, translate_union, translate_counter_shift, reg1Block, %s,\n'
                '    %sPullS, translate_ofRows]\n  norm_num\n' % (j, name, sa, P, P, sa, P))
            special = name
        # generic atoms must otherwise match exactly
        for e, c in list(A):
            if c is None:
                assert (e, None) in B, ('unmatched generic atom', j, e)
        self._glue_core(j, A, B, special)

    def _glue_core(self, j, A, B, special):
        A, B = list(A), list(B)
        P = self.P
        common = []
        for e, c in list(A):
            for k_, (e2, c2) in enumerate(B):
                if e2 == e:
                    common.append(e)
                    A.remove((e, c))
                    del B[k_]
                    break
        nodes = [('A', e, c) for e, c in A] + [('B', e, c) for e, c in B]
        par = list(range(len(nodes)))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for x in range(len(nodes)):
            for y in range(x):
                if nodes[x][2] & nodes[y][2]:
                    par[find(x)] = find(y)
        cl = {}
        for x in range(len(nodes)):
            cl.setdefault(find(x), []).append(nodes[x])
        eqs, lg, rg = [], [], []
        for ci, mem in enumerate(cl.values()):
            ea = [(e, c) for s_, e, c in mem if s_ == 'A']
            eb = [(e, c) for s_, e, c in mem if s_ == 'B']
            ua = set().union(*[c for _, c in ea]) if ea else set()
            ub = set().union(*[c for _, c in eb]) if eb else set()
            if ua != ub or not ea or not eb:
                raise ValueError(('glue mismatch', j, [e for e, _ in ea], [e for e, _ in eb]))
            za, zb_ = '%sZ%d_%da' % (P, j, ci), '%sZ%d_%db' % (P, j, ci)
            self.union_to(ea, ua, za, 'Glue %d, cluster %d, before.' % (j, ci))
            self.union_to(eb, ub, zb_, 'Glue %d, cluster %d, after.' % (j, ci))
            eqs.append('%s, ← %s' % (za, zb_))
            pe = lambda es: '(' + ' ∪ '.join(e if not e.startswith('conway') else '(%s)' % e for e, _ in es) + ')'
            lg.append(pe(ea))
            rg.append(pe(eb))
        com = ['(%s)' % e if e.startswith('conway') or ' ' in e else e for e in common]
        L = ' ∪ '.join(lg + com)
        R = ' ∪ '.join(rg + com)
        unf = ['%sL%d' % (P, j), '%sL%d' % (P, j + 1)] + ['%sG%d' % (P, i) for i in range(len(self.pg))]
        body = ('  simp only [%s, Proc.stop_cons, Proc.start_cons, Proc.stop_nil, Proc.start_nil,\n'
                '    Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty]\n' % ', '.join(unf))
        last = ('by rw [← %s k]; ac_rfl' % special) if special else 'by ac_rfl'
        if eqs:
            body += ('  calc _ = %s := by ac_rfl\n    _ = %s := by rw [%s]\n    _ = _ := %s\n'
                     % (L, R, ', '.join(eqs), last))
        else:
            body += ('  all_goals ac_rfl\n' if not special else '  rw [← %s k]\n  all_goals ac_rfl\n' % special)
        self.gluelem.append('set_option maxRecDepth 100000 in\n/-- The end of segment %d is the start of segment %d. -/\n'
                            'theorem %sGl%d (k : ℕ) : Proc.stop (%sL%d k) = Proc.start (%sL%d k) := by\n%s'
                            % (j, j + 1, P, j, P, j, P, j + 1, body))

    # ------------------------------------------------------------ run
    def run(self):
        P = self.P
        segs = self.plan['segs']
        self._phases, self._still, self._flyer = set(), set(), set()
        self.lemmas, self.seglem, self.gluelem = [], [], []
        self.lemmas += self.pull_lemmas()
        ends, chunks = [], []
        for j, seg in enumerate(segs):
            mark = len(self.seglem)
            ends.append(self.segment(j, seg))
            chunks.append((mark, len(self.seglem)))
        for j in range(len(segs) - 1):
            self.glue(j, ends[j][1], ends[j + 1][0])
        ns = [seg['b'] - seg['a'] for seg in segs]
        S = len(segs)
        tot = sum(ns)
        expr = str(ns[0])
        for x in ns[1:]:
            expr = '%d + (%s)' % (x, expr)
        rws = ['%sSeg0 k hk |>.evolve_eq' % P]
        rws = ['(%sSeg0 k hk).evolve_eq' % P]
        for j in range(1, S):
            rws += ['%sGl%d k' % (P, j - 1), '(%sSeg%d k hk).evolve_eq' % (P, j)]
        final = ('set_option maxRecDepth 100000 in\n/-- **The run** with the block at `k`: %d generations, %d segments. -/\n'
                 'theorem %sRun (k : ℕ) (hk : %d ≤ k) :\n    conway.evolve %d (Proc.start (%sL0 k)) = Proc.stop (%sL%d k) := by\n'
                 '  rw [show %d = %s by norm_num]\n  rw [%s]\n  rw [%s]\n'
                 % (tot, S, P, self.K0, tot, P, P, S - 1, tot, expr,
                    ', '.join(['Rule.evolve_add'] * (S - 1)) if S > 1 else 'Rule.evolve_zero',
                    ',\n    '.join(rws)))
        final += '\n' + self.tail(segs)
        return chunks, final

    def tail(self, segs):
        """The last 4 k generations (the salvo finishes) and the statement of the whole run."""
        P = self.P
        last = segs[-1]
        Ts = self.plan['Ts']
        sE = (last['b'] - Ts) % 30
        assert sE == 0
        M = last['b'] - self.ts
        flights = [p for p in last['procs'] if p['kind'] == 'flight' and not is_salvo(p)]
        others = [p for p in last['procs'] if p['kind'] in ('cert', 'still') and p['start']]
        assert len(flights) <= 1 and not others, 'the tail expects at most one output glider'
        if not flights:
            return self.tail_noout(segs, M)
        f = flights[0]
        N1 = self.atom(f['stop'])
        cells = set(f['stop'])
        c = set(cells)
        pb = None
        for _ in range(4):
            b = window_bbox(c)
            pb = b if pb is None else (min(pb[0], b[0]), min(pb[1], b[1]), max(pb[2], b[2]), max(pb[3], b[3]))
            c = evolve(c, 1)
        (dx, dy) = f['v']
        assert (dx, dy) == (1, 1)
        if N1 not in self._flyer:
            self._flyer.add(N1)
            self.lemmas.append('/-- The output glider moves by `(1, 1)` every four generations. -/\n'
                               'theorem %s_four : conway.evolve 4 %s = translate (1, 1) %s := by\n'
                               '  rw [%s, translate_ofRows]\n  life_cert\n' % (N1, N1, N1, N1))
            self.lemmas.append('/-- During its first four generations the output glider stays in a box. -/\n'
                               'theorem %s_box (r : ℕ) (hr : r < 4) :\n    (conway.evolve r %s : Set Cell) ⊆ %s := by\n'
                               '  interval_cases r <;> (rw [%s]; life_eval; exact coe_ofRows_subset_box rfl)\n'
                               % (N1, N1, box(pb), N1))
        ftail = {'kind': 'flight', 'v': (1, 1), 'pb': pb}
        allg = '%sPieces' % P
        out = []
        out.append('/-- The tail: %s generations more, block at `k`. -/\n'
                   'def %sLT (k : ℕ) : List (Proc (4 * k)) :=\n'
                   '  [{ P := conway.evolve %d (%sPullX k), Q := conway.evolve (4 * k + %d) (%sPullX k),\n'
                   '     F := fun i => %sPullG k (i + %d), reaction := trajectory_reaction (%sPullAll k) %d (4 * k) },\n'
                   '   { P := %s, Q := translate ((k : ℤ) * 1, (k : ℤ) * 1) (conway.evolve 0 %s),\n'
                   '     F := fun i => %s, reaction := flight_reaction %s_four %s_box k 0 rfl },\n'
                   '   Piece.bundle %s %sPieces_sep 0 (4 * k) ((4 * k + 0) %% 30) rfl]\n'
                   % ('4 k', P, M, P, M, P, P, M, P, M, N1, N1, self.fp(ftail, 'i'), N1, N1, allg, P))
        idle_all = list(range(len(self.pg)))
        g1 = '(fun i _hi => %s)' % self.gfar(M, self.fp(ftail, 'i'))
        gb = 'Piece.indep_bundle _ _ _ _ _ _\n        ⟨' + ',\n         '.join(
            ['(fun i _hi => %s)' % self.gfar(M, box(self.pg[gi][2])) for gi in idle_all] + ['trivial']) + '⟩'
        fb = self.indep_bundle(ftail, idle_all)
        parts = ['⟨' + ',\n      '.join([g1, gb, 'trivial']) + '⟩', '⟨' + fb + ', trivial⟩', 'trivial']
        out.append('set_option maxRecDepth 100000 in\n/-- **The tail** of the run: the salvo finishes for every `k`. -/\n'
                   'theorem %sTail (k : ℕ) (_hk : %d ≤ k) :\n'
                   '    Reaction (Proc.start (%sLT k)) (Proc.stop (%sLT k)) (4 * k) (Proc.foot (%sLT k)) :=\n'
                   '  Reaction.parList _ (PairR.pairwise\n    %s)\n'
                   % (P, self.K0, P, P, P, self.nest(parts, '    ')))
        unfG = ', '.join('%sG%d' % (P, i) for i in range(len(self.pg)))
        S = len(segs)
        out.append('set_option maxRecDepth 100000 in\n/-- The end of the run is the start of the tail. -/\n'
                   'theorem %sGlT (k : ℕ) : Proc.stop (%sL%d k) = Proc.start (%sLT k) := by\n'
                   '  simp only [%sL%d, %sLT, %s, %s, Proc.stop_cons, Proc.start_cons, Proc.stop_nil,\n'
                   '    Proc.start_nil, Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty]\n'
                   '  all_goals ac_rfl\n' % (P, P, S - 1, P, P, S - 1, P, allg, unfG))
        c0, n0 = self.c0, self.n0
        out.append('/-- The salvo has pulled the block from `k` to `k - 1`. -/\n'
                   'theorem %sPullEnd (k : ℕ) : conway.evolve (4 * k + %d) (%sPullX k) = reg1Block (↑k %s) := by\n'
                   '  rw [show 4 * k + %d = (k + %d) * 4 + %d by omega, %sPullX,\n'
                   '    salvo_world_end %sPullS_four %sPullS_box %sPullHz (by norm_num) _ _ _ _ (by norm_num),\n'
                   '    reg1Block, counter, counter, translate_ofRows, translate_ofRows]\n'
                   '  congr 1 <;> push_cast <;> omega\n'
                   % (P, M, P, '- 1' if self.d == -1 else '+ 1', M, c0, M - 4 * c0, P, P, P, P))
        rest = ' ∪ ('.join('%sR%d' % (P, i) for i in range(len(self.pg))) + ')' * (len(self.pg) - 1)
        first = segs[0]
        ctrl = [p for p in first['procs'] if p['kind'] == 'flight']
        assert len(ctrl) == 1
        C = self.atom(ctrl[0]['start'])
        out.append('/-- The whole circuit at rest at the reference time. -/\ndef %sRest : Finset Cell :=\n  %s\n'
                   % (P, rest))
        tot = sum(sg['b'] - sg['a'] for sg in segs)
        unfA = sorted({C, N1})
        out.append(
            'set_option maxRecDepth 100000 in\n'
            '/-- **The run for every position `k >= %d`**: the circuit at rest, its control glider and the\n'
            'block at `k` evolve, in `4 k + %d` generations, into the circuit (in its cycle), the block at\n'
            '`k - 1` and the output glider. -/\n'
            'theorem %sAll (k : ℕ) (hk : %d ≤ k) :\n'
            '    conway.evolve (4 * k + %d) (%sRest ∪ %s ∪ reg1Block ↑k) =\n'
            '      conway.evolve (4 * k) %sRest ∪ reg1Block (↑k - 1) ∪\n'
            '        translate ((k : ℤ), (k : ℤ)) (%s) := by\n'
            '  have hs : Proc.start (%sL0 k) = %sRest ∪ %s ∪ reg1Block ↑k := by\n'
            '    simp only [%sL0, %sRest, %s, %s, Proc.start_cons, Proc.start_nil, Piece.bundle, Piece.idle,\n'
            '      List.map_cons, List.map_nil, union_empty, Rule.evolve_zero]\n    ac_rfl\n'
            '  have hb := (Piece.bundle %s %sPieces_sep 0 (4 * k) ((4 * k + 0) %% 30) rfl).reaction.evolve_eq\n'
            '  simp only [%s, %s, Proc.start_cons, Proc.start_nil, Proc.stop_cons, Proc.stop_nil,\n'
            '    Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty, Rule.evolve_zero] at hb\n'
            '  rw [Rule.evolve_add, ← hs, %sRun k hk, %sGlT k, (%sTail k hk).evolve_eq, %sRest, hb, ← %sPullEnd k]\n'
            '  simp only [%sLT, %s, %s, %s, Proc.stop_cons, Proc.stop_nil, Piece.bundle, Piece.idle,\n'
            '    List.map_cons, List.map_nil, union_empty, Rule.evolve_zero, mul_one]\n'
            '  ac_rfl\n'
            % (self.K0, tot, P, self.K0, tot, P, ofrows(set(ctrl[0]['start'])), P, ofrows(cells),
               P, P, ofrows(set(ctrl[0]['start'])), P, P, C, unfG, allg, P, allg, unfG, P, P, P, P, P, P, allg, unfG, N1))
        # the atoms in the statement are written out
        return '\n'.join(out).replace('%sRest ∪ %s ∪ reg1Block ↑k := by' % (P, C), '%sRest ∪ %s ∪ reg1Block ↑k := by' % (P, C))


def _tail_noout(self, segs, M):
    """Tail and statement for a run whose only result is the moved block (an increment)."""
    P = self.P
    allg = '%sPieces' % P
    out = []
    out.append('/-- The tail: 4 k generations more, block at `k`. -/\n'
               'def %sLT (k : ℕ) : List (Proc (4 * k)) :=\n'
               '  [{ P := conway.evolve %d (%sPullX k), Q := conway.evolve (4 * k + %d) (%sPullX k),\n'
               '     F := fun i => %sPullG k (i + %d), reaction := trajectory_reaction (%sPullAll k) %d (4 * k) },\n'
               '   Piece.bundle %s %sPieces_sep 0 (4 * k) ((4 * k + 0) %% 30) rfl]\n'
               % (P, M, P, M, P, P, M, P, M, allg, P))
    idle_all = list(range(len(self.pg)))
    gb = 'Piece.indep_bundle _ _ _ _ _ _\n        ⟨' + ',\n         '.join(
        ['(fun i _hi => %s)' % self.gfar(M, box(self.pg[gi][2])) for gi in idle_all] + ['trivial']) + '⟩'
    parts = ['⟨' + gb + ', trivial⟩', 'trivial']
    out.append('set_option maxRecDepth 100000 in\n/-- **The tail** of the run: the salvo finishes for every `k`. -/\n'
               'theorem %sTail (k : ℕ) (_hk : %d ≤ k) :\n'
               '    Reaction (Proc.start (%sLT k)) (Proc.stop (%sLT k)) (4 * k) (Proc.foot (%sLT k)) :=\n'
               '  Reaction.parList _ (PairR.pairwise\n    %s)\n'
               % (P, self.K0, P, P, P, self.nest(parts, '    ')))
    unfG = ', '.join('%sG%d' % (P, i) for i in range(len(self.pg)))
    S = len(segs)
    out.append('set_option maxRecDepth 100000 in\n/-- The end of the run is the start of the tail. -/\n'
               'theorem %sGlT (k : ℕ) : Proc.stop (%sL%d k) = Proc.start (%sLT k) := by\n'
               '  simp only [%sL%d, %sLT, %s, %s, Proc.stop_cons, Proc.start_cons, Proc.stop_nil,\n'
               '    Proc.start_nil, Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty]\n'
               '  all_goals ac_rfl\n' % (P, P, S - 1, P, P, S - 1, P, allg, unfG))
    c0, n0 = self.c0, self.n0
    sgn = '- 1' if self.d == -1 else '+ 1'
    out.append('/-- The salvo has moved the block. -/\n'
               'theorem %sPullEnd (k : ℕ) : conway.evolve (4 * k + %d) (%sPullX k) = reg1Block (↑k %s) := by\n'
               '  rw [show 4 * k + %d = (k + %d) * 4 + %d by omega, %sPullX,\n'
               '    salvo_world_end %sPullS_four %sPullS_box %sPullHz (by norm_num) _ _ _ _ (by norm_num),\n'
               '    reg1Block, counter, counter, translate_ofRows, translate_ofRows]\n'
               '  congr 1 <;> push_cast <;> omega\n'
               % (P, M, P, sgn, M, c0, M - 4 * c0, P, P, P, P))
    rest = ' ∪ ('.join('%sR%d' % (P, i) for i in range(len(self.pg))) + ')' * (len(self.pg) - 1)
    first = segs[0]
    ctrl = [p for p in first['procs'] if p['kind'] == 'flight']
    assert len(ctrl) == 1
    C = self.atom(ctrl[0]['start'])
    lit = ofrows(set(ctrl[0]['start']))
    out.append('/-- The whole circuit at rest at the reference time. -/\ndef %sRest : Finset Cell :=\n  %s\n'
               % (P, rest))
    tot = sum(sg['b'] - sg['a'] for sg in segs)
    out.append(
        'set_option maxRecDepth 100000 in\n'
        '/-- **The run for every position `k >= %d`**: the circuit at rest, its control glider and the\n'
        'block at `k` evolve, in `4 k + %d` generations, into the circuit (in its cycle) and the block\n'
        'at `k %s`. -/\n'
        'theorem %sAll (k : ℕ) (hk : %d ≤ k) :\n'
        '    conway.evolve (4 * k + %d) (%sRest ∪ %s ∪ reg1Block ↑k) =\n'
        '      conway.evolve (4 * k) %sRest ∪ reg1Block (↑k %s) := by\n'
        '  have hs : Proc.start (%sL0 k) = %sRest ∪ %s ∪ reg1Block ↑k := by\n'
        '    simp only [%sL0, %sRest, %s, %s, Proc.start_cons, Proc.start_nil, Piece.bundle, Piece.idle,\n'
        '      List.map_cons, List.map_nil, union_empty, Rule.evolve_zero]\n    ac_rfl\n'
        '  have hb := (Piece.bundle %s %sPieces_sep 0 (4 * k) ((4 * k + 0) %% 30) rfl).reaction.evolve_eq\n'
        '  simp only [%s, %s, Proc.start_cons, Proc.start_nil, Proc.stop_cons, Proc.stop_nil,\n'
        '    Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty, Rule.evolve_zero] at hb\n'
        '  rw [Rule.evolve_add, ← hs, %sRun k hk, %sGlT k, (%sTail k hk).evolve_eq, %sRest, hb, ← %sPullEnd k]\n'
        '  simp only [%sLT, %s, %s, Proc.stop_cons, Proc.stop_nil, Piece.bundle, Piece.idle,\n'
        '    List.map_cons, List.map_nil, union_empty]\n'
        '  ac_rfl\n'
        % (self.K0, tot, sgn, P, self.K0, tot, P, lit, P, sgn, P, P, lit, P, P, C, unfG, allg, P, allg, unfG,
           P, P, P, P, P, P, allg, unfG))
    return '\n'.join(out)


GenEmitter.tail_noout = _tail_noout


def window_bbox(c):
    xs = [q[0] for q in c]
    ys = [q[1] for q in c]
    return (min(xs), min(ys), max(xs), max(ys))


def main():
    plan_path, prefix, moddir, K0 = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    per = int(sys.argv[5]) if len(sys.argv) > 5 else 8
    dd = int(sys.argv[6]) if len(sys.argv) > 6 else -1
    plan = pickle.load(open(plan_path, 'rb'))
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'life_machine'))
    from net import piece_cells
    em = GenEmitter(plan, prefix, K0, dd)
    em.rest = {}
    Ts = plan['Ts']
    for name, kind, env, members in plan['groups']:
        if kind != 'piece':
            continue
        for s in range(30):
            cs = set()
            for i in members:
                cs |= piece_cells(plan['pieces'][i], Ts + s)
            em.rest[(name, s)] = cs
    pieces_txt = em.piece_defs({g[0]: em.rest[(g[0], 0)] for g in em.pg})
    chunks, final = em.run()
    Cap = prefix[0].upper() + prefix[1:]
    base = 'LeanTheory.Theory.Life.Gen.'
    os.makedirs(moddir, exist_ok=True)
    doc = ('# Generated certificate `%s`: %s\n\nGenerated by `scripts/life_cert/emit_generic.py` from a segment\n'
           'plan (`scripts/life_cert/plan.py`); the generator is untrusted, Lean checks every step.')
    opts = 'set_option linter.style.longLine false\n\n'
    with open(os.path.join(moddir, Cap + 'Data.lean'), 'w') as f:
        f.write(HEADER % ('public import LeanTheory.Theory.Life.Network\npublic import LeanTheory.Theory.Life.Register1Ops',
                          doc % (prefix, 'the pieces and configurations')))
        f.write(opts)
        f.write('\n'.join(pieces_txt + em.atom_defs + em.lemmas))
        f.write(FOOTER)
    files = []
    for c in range(0, len(chunks), per):
        lo, hi = chunks[c][0], chunks[min(c + per, len(chunks)) - 1][1]
        nm = '%sSeg%d' % (Cap, c // per)
        files.append(nm)
        with open(os.path.join(moddir, nm + '.lean'), 'w') as f:
            f.write(HEADER % ('public import %s%sData' % (base, Cap),
                              doc % (prefix, 'segments %d to %d' % (c, min(c + per, len(chunks)) - 1))))
            f.write(opts)
            f.write('\n'.join(em.seglem[lo:hi]))
            f.write(FOOTER)
    with open(os.path.join(moddir, Cap + 'Run.lean'), 'w') as f:
        f.write(HEADER % ('\n'.join('public import %s%s' % (base, nm) for nm in files),
                          doc % (prefix, 'the glue and the whole run')))
        f.write('set_option linter.style.longLine false\nset_option linter.unusedSimpArgs false\n'
                'set_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n\n')
        f.write('\n'.join(em.gluelem + [final]))
        f.write(FOOTER)
    print('segments', len(chunks), 'atoms', len(em.atoms), 'salvo from segment', em.js, 'n0', em.n0, 'files', files)


if __name__ == '__main__':
    main()
