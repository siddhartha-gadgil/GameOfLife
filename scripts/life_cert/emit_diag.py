#!/usr/bin/env python3
"""Lean emitter for the zero test with the register diagonal as a generic process (research notes
N-20, N-22).  Input: the plan of the run WITHOUT the block, with a boundary MERGE where the new pull
salvo joins the diagonal.  The diagonal is `conway.evolve (m0 + o) (diagW q K)` (queue q, block K,
virtual time m0) before the merge and `diagW (q ++ [(regPull, eP)]) K` after it; every other process
is separated from its strip `wStrip` in u or in v (flights carry both an x-y box and a diagonal
box).  Untrusted generator: Lean checks everything.

Usage: emit_diag.py PLAN.pkl PREFIX MODULEDIR MERGE [SEGS_PER_FILE]"""
import os
import pickle
import sys
from emit import (Emitter, HEADER, FOOTER, z, ofrows, ofrows_ml, box, far_disj, evolve, window_of_cells)

VX, VY = 148, 240
BAND = (-110, -80)
PULL = {(-1, 5), (1, 5), (0, 6), (1, 6), (9, 6), (1, 7), (6, 7), (8, 7), (9, 7), (8, 8), (9, 8)}  # placeholder


def is_salvo(p):
    return p['kind'] == 'flight' and p['v'] == (1, 1) and \
        all(BAND[0] <= x - y <= BAND[1] for x, y in p['start'])


def bbox(c):
    xs = [q[0] for q in c]
    ys = [q[1] for q in c]
    return (min(xs), min(ys), max(xs), max(ys))


def uvrange(cells):
    us = [x - y for x, y in cells]
    vs = [x + y for x, y in cells]
    return (min(us), max(us), min(vs), max(vs))


class DiagEmitter(Emitter):
    def __init__(self, plan, prefix, merge, kind='pull', phase=0):
        super().__init__(plan, prefix)
        self.kind = kind
        self.SN = 'regPull' if kind == 'pull' else 'regPush'
        self.SD = 'dz2gPullS' if kind == 'pull' else 'dz2jPullS'
        self.SW = (-1, 5, [5, 518, 642, 768]) if kind == 'pull' else (-6, -7, [320, 384, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 16390, 32770, 57344])
        if phase:
            import re
            src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'LeanTheory',
                                    'Theory', 'Life', 'SalvoPhases.lean')).read()
            self.SN = 'reg%sP%d' % ('Pull' if kind == 'pull' else 'Push', phase)
            self.SD = self.SN + 'S'
            m = re.search(r'def %s : Finset Cell := ofRows (\(?-?\d+\)?) (\(?-?\d+\)?) \[([^\]]*)\]' % self.SD, src)
            self.SW = (int(m.group(1).strip('()')), int(m.group(2).strip('()')), [int(x) for x in m.group(3).split(',')])
        segs = plan['segs']
        self.jM = [j for j, sg in enumerate(segs) if sg['a'] == merge][0]
        self.oM = merge - plan['Ts']
        sal = set()
        for p in segs[self.jM]['procs']:
            if is_salvo(p):
                sal |= set(p['start'])
        self.salvo_w = sal
        for sg in segs[self.jM:]:
            assert any(is_salvo(p) for p in sg['procs'])
        # the offset of the salvo at the merge, relative to regPull.S = dz2gPullS
        S = cells_of(*self.SW)
        loc = {(x - VX, y - VY) for x, y in sal}
        es = [e for e in range(-50, 300) if {(x - e, y - e) for x, y in S} == loc]
        assert len(es) == 1, ('salvo does not match regPull', es)
        self.e0 = es[0]

    # ---------------------------------------------------------------- footprints and separation
    def gen_lower(self, j, i_rel, o):
        """Lower bound of x + y of the diagonal strip at generation i_rel of segment j (offset o)."""
        if j < self.jM:
            vs = 18 + 2 * ((i_rel + o) // 4)
        else:
            vs = -34 + 2 * ((i_rel + o - self.oM) // 4)
        return min(vs, 18) + 388

    def proc_geom(self, p, i):
        """(x-y box, (umin, umax, vmin, vmax) or None) of a process at generation i of its segment."""
        if p['kind'] == 'flight':
            (dx, dy), pb, uv = p['v'], p['pb'], p['uv']
            q = i // 4
            return ((pb[0] + q * dx, pb[1] + q * dy, pb[2] + q * dx, pb[3] + q * dy),
                    (uv[0] + q * (dx - dy), uv[1] + q * (dx - dy), uv[2] + q * (dx + dy), uv[3] + q * (dx + dy)))
        return (p['box'], None)

    def gen_sep(self, j, o, n, p, xybox=None):
        """Lean term: FarApart (diagonal strip) (footprint of p, or the box xybox), for i < n."""
        u_ok = v_ok = uv_ok = uvu_ok = True
        for i in range(n):
            lo = self.gen_lower(j, i, o)
            if xybox is not None:
                b, uv = xybox, None
            else:
                b, uv = self.proc_geom(p, i)
            if not (b[2] - b[1] + 4 < -113 or -65 < b[0] - b[3]):
                u_ok = False
            if not (b[2] + b[3] + 4 < lo):
                v_ok = False
            if uv is None or not (uv[3] + 4 < lo):
                uv_ok = False
            if uv is None or not (uv[1] + 4 < -113 or -65 < uv[0]):
                uvu_ok = False
        flight = xybox is None and p['kind'] == 'flight'
        VS = 'Vs' if j < self.jM else "Vs'"
        strip = 'wStrip %s Vb (i + (m0 + %d))' % (VS, o)
        bx = box(xybox if xybox is not None else (p['box'] if not flight else p['pb']))
        if u_ok:
            if flight:
                return "(FarApart.inter_left (farApart_box_wStrip_u (by omega))).symm'"
            return "((farApart_box_wStrip_u (by omega)) : FarApart 2 (%s) (%s)).symm'" % (bx, strip)
        if v_ok:
            if flight:
                return "(FarApart.inter_left (farApart_box_wStrip_v (by omega) (by omega))).symm'"
            return "((farApart_box_wStrip_v (by omega) (by omega)) : FarApart 2 (%s) (%s)).symm'" % (bx, strip)
        if flight and uv_ok:
            return "(FarApart.inter_left' (farApart_uv_wStrip_v (by omega) (by omega))).symm'"
        if flight and uvu_ok:
            return "(FarApart.inter_left' (farApart_uv_wStrip_u (by omega))).symm'"
        raise ValueError(('no separation from the diagonal', j, p.get('kind'), p.get('group'),
                          xybox or self.proc_geom(p, 0)))

    def wrap(self, xyterm, pf, qf):
        """Wrap a separation of the x-y boxes for flights, whose footprint is box ∩ diagonal box."""
        t = xyterm
        if pf:
            t = '(FarApart.inter_left %s)' % t
        if qf:
            t = '(FarApart.inter_right %s)' % t
        return t

    def indep(self, p, q):
        pf, qf = p['kind'] == 'flight', q['kind'] == 'flight'
        if not pf and not qf:
            return '(fun _ _ => (Box.farApart (%s) : FarApart 2 (%s) (%s)))' % (
                far_disj(p['box'], q['box']), box(p['box']), box(q['box']))
        inner = '(Box.farApart (by omega) : FarApart 2 (%s) (%s))' % (self.fp(p, 'i'), self.fp(q, 'i'))
        return '(fun i _hi => %s)' % self.wrap(inner, pf, qf)

    def indep_bundle(self, p, idle):
        terms = []
        pf = p['kind'] == 'flight'
        for gi in idle:
            env = self.pg[gi][2]
            if not pf:
                terms.append('(fun _ _ => (Box.farApart (%s) : FarApart 2 (%s) (%s)))'
                             % (far_disj(p['box'], env), box(p['box']), box(env)))
            else:
                terms.append('(fun i _hi => FarApart.inter_left (Box.farApart (by omega) : FarApart 2 (%s) (%s)))'
                             % (self.fp(p, 'i'), box(env)))
        if not terms:
            return 'Piece.indep_bundle _ _ _ _ _ _ trivial'
        return 'Piece.indep_bundle _ _ _ _ _ _\n        ⟨' + ',\n         '.join(terms + ['trivial']) + '⟩'

    # ---------------------------------------------------------------- flights with both footprints
    def mover(self, j, m, p, n):
        if p['kind'] != 'flight':
            return super().mover(j, m, p, n)
        P = self.P
        A = self.atom(p['start'])
        B = self.atom(p['stop'])
        (dx, dy), pb = p['v'], p['pb']
        c = set(p['start'])
        uv = None
        for _ in range(4):
            r = uvrange(c)
            uv = r if uv is None else (min(uv[0], r[0]), max(uv[1], r[1]), min(uv[2], r[2]), max(uv[3], r[3]))
            c = evolve(c, 1)
        p['uv'] = uv
        if A not in self._flyer:
            self._flyer.add(A)
            self.lemmas.append('/-- A flying object of the run moves by `(%d, %d)` every four generations. -/\n'
                               'theorem %s_four : conway.evolve 4 %s = translate (%s, %s) %s := by\n'
                               '  rw [%s, translate_ofRows]\n  life_cert\n' % (dx, dy, A, A, z(dx), z(dy), A, A))
            self.lemmas.append('/-- During its first four generations the object stays in a box. -/\n'
                               'theorem %s_box (r : ℕ) (hr : r < 4) :\n    (conway.evolve r %s : Set Cell) ⊆ %s := by\n'
                               '  interval_cases r <;> (rw [%s]; life_eval; exact coe_ofRows_subset_box rfl)\n'
                               % (A, A, box(pb), A))
            self.lemmas.append('/-- During its first four generations the object stays in a diagonal box. -/\n'
                               'theorem %s_uv (r : ℕ) (hr : r < 4) :\n    (conway.evolve r %s : Set Cell) ⊆ UVBox %s %s %s %s := by\n'
                               '  interval_cases r <;> (rw [%s]; life_eval; exact coe_ofRows_subset_uv rfl)\n'
                               % (A, A, z(uv[0]), z(uv[1]), z(uv[2]), z(uv[3]), A))
        q, r = divmod(n, 4)
        name = '%sF%d_%d' % (P, j, m)
        if r == 0:
            ev = 'rw [Rule.evolve_zero, %s, translate_ofRows, %s]' % (A, B)
        else:
            W = ofrows(evolve(set(p['start']), r))
            ev = ('rw [show conway.evolve %d %s = %s by rw [%s]; life_cert,\n    translate_ofRows, %s]'
                  % (r, A, W, A, B))
        self.seglem.append('/-- End of a flight (segment %d, process %d). -/\n'
                           'theorem %se : translate (((%d : ℕ) : ℤ) * %s, ((%d : ℕ) : ℤ) * %s) (conway.evolve %d %s) = %s := by\n'
                           '  %s\n  norm_num\n' % (j, m, name, q, z(dx), q, z(dy), r, A, B, ev))
        F = self.fpb(p, 'i')
        self.seglem.append('/-- A flight (segment %d, process %d). -/\ntheorem %s :\n    Reaction %s %s %d (fun i => %s) :=\n'
                           '  flight_reaction_xyuv %s_four %s_box %s_uv %d %d %se\n'
                           % (j, m, name, A, B, n, F, A, A, A, q, r, name))
        return '{ P := %s, Q := %s, F := fun i => %s, reaction := %s }' % (A, B, F, name)

    def fpb(self, p, iv):
        (dx, dy), uv = p['v'], p['uv']
        q = '((%s / 4 : ℕ) : ℤ)' % iv
        return '%s ∩ UVBox (%s + %s * %s) (%s + %s * %s) (%s + %s * %s) (%s + %s * %s)' % (
            self.fp(p, iv), z(uv[0]), q, z(dx - dy), z(uv[1]), q, z(dx - dy), z(uv[2]), q, z(dx + dy),
            z(uv[3]), q, z(dx + dy))

    # ---------------------------------------------------------------- segments
    def qexpr(self, j):
        return 'q' if j < self.jM else '(q ++ [(@SN@, %s)])' % self.eP()

    def eP(self):
        return '((%d : ℤ) + (((m0 + %d) / 4 : ℕ) : ℤ))' % (self.e0, self.oM)

    def segment(self, j, seg):
        P = self.P
        Ts = self.plan['Ts']
        a, b = seg['a'], seg['b']
        n = b - a
        o, o2 = a - Ts, b - Ts
        s, s2 = o % 30, o2 % 30
        movers = [p for p in seg['procs'] if p['kind'] in ('cert', 'flight', 'still') and p['start']
                  and not (j >= self.jM and is_salvo(p))]
        idle = sorted(self.gi[p['group']] for p in seg['procs'] if p['kind'] == 'idle')
        lits = [self.mover(j, m, p, n) for m, p in enumerate(movers)]
        Q = self.qexpr(j)
        hv = 'hv' if j < self.jM else 'hv\''
        Vs = 'Vs' if j < self.jM else 'Vs\''
        glit = ('{ P := conway.evolve (m0 + %d) (diagW %s K), Q := conway.evolve (m0 + %d) (diagW %s K),\n'
                '     F := fun i => wStrip %s Vb (i + (m0 + %d)),\n'
                '     reaction := diagW_reaction %s (m0 + %d) %d (m0 + %d) (by ring) }'
                % (o, Q, o2, Q, Vs, o, hv, o, n, o2))
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
        args = '(q : List (Salvo × ℤ)) (K Vs Vb Vs\' : ℤ) (m0 : ℕ)'
        self.seglem.append('/-- The processes of segment %d (generations %d to %d of the run). -/\n'
                           'def %sL%d %s\n    (hv : DiagValid regParams Vs Vb K q)\n'
                           '    (hv\' : DiagValid regParams Vs\' Vb K (q ++ [(@SN@, %s)])) :\n'
                           '    List (Proc %d) :=\n  [%s]\n'
                           % (j, a, b, P, j, args, self.eP(), n, ',\n   '.join([glit] + lits + [bundle])))
        gterms = ['(fun i _hi => %s)' % self.gen_sep(j, o, n, q) for q in movers]
        bterms = ['(fun i _hi => %s)' % self.gen_sep(j, o, n, None, self.pg[gi][2]) for gi in idle]
        gb = ('Piece.indep_bundle _ _ _ _ _ _\n        ⟨' + ',\n         '.join(bterms + ['trivial']) + '⟩'
              if bterms else 'Piece.indep_bundle _ _ _ _ _ _ trivial')
        parts = ['⟨' + ',\n      '.join(gterms + [gb, 'trivial']) + '⟩']
        for x, p in enumerate(movers):
            terms = [self.indep(p, q) for q in movers[x + 1:]] + [self.indep_bundle(p, idle)]
            parts.append('⟨' + ',\n      '.join(terms + ['trivial']) + '⟩')
        parts.append('trivial')
        self.seglem.append('set_option maxRecDepth 100000 in\n/-- **Segment %d** of the run with the register diagonal. -/\n'
                           'theorem %sSeg%d %s\n    (hv : DiagValid regParams Vs Vb K q)\n'
                           '    (hv\' : DiagValid regParams Vs\' Vb K (q ++ [(@SN@, %s)]))\n'
                           '    (hm : (m0 + @OM@) %% 4 = 0) (hVb : 18 ≤ Vb) (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ))\n'
                           '    (hVs\' : -34 ≤ Vs\' + 2 * (((m0 + %d) / 4 : ℕ) : ℤ)) :\n'
                           '    Reaction (Proc.start (%sL%d q K Vs Vb Vs\' m0 hv hv\'))\n'
                           '      (Proc.stop (%sL%d q K Vs Vb Vs\' m0 hv hv\')) %d\n'
                           '      (Proc.foot (%sL%d q K Vs Vb Vs\' m0 hv hv\')) :=\n'
                           '  Reaction.parList _ (PairR.pairwise\n    %s)\n'
                           % (j, P, j, args, self.eP(), self.oM, P, j, P, j, n, P, j, self.nest(parts, '    ')))
        gstart = 'conway.evolve (m0 + %d) (diagW %s K)' % (o, Q)
        gstop = 'conway.evolve (m0 + %d) (diagW %s K)' % (o2, Q)
        start = [(gstart, None)] + [(self.atom(p['start']), set(p['start'])) for p in movers]
        start += [('conway.evolve %d %sR%d' % (s, P, i), self.rest_cells(i, a)) for i in idle]
        stop = [(gstop, None)] + [(self.atom(p['stop'] if p['kind'] != 'still' else p['start']),
                                   set(p['stop'] if p['kind'] != 'still' else p['start'])) for p in movers]
        stop += [('conway.evolve %d %sR%d' % (s2, P, i), self.rest_cells(i, b)) for i in idle]
        return start, stop

    # ---------------------------------------------------------------- glue
    def glue(self, j, stop, start):
        P = self.P
        A, B = list(stop), list(start)
        special = None
        if j + 1 == self.jM:
            gq = 'conway.evolve (m0 + %d) (diagW q K)' % self.oM
            gq2 = 'conway.evolve (m0 + %d) (diagW (q ++ [(@SN@, %s)]) K)' % (self.oM, self.eP())
            B.remove((gq2, None))
            B.append((gq, None))
            sa = self.atom(self.salvo_w)
            B.append((sa, set(self.salvo_w)))
            name = '%sMrg' % P
            self.gluelem.append(
                'set_option maxRecDepth 100000 in\n/-- The pull salvo joins the register diagonal. -/\n'
                'theorem %s (q : List (Salvo × ℤ)) (K Vs Vb : ℤ) (m0 : ℕ) (hv : DiagValid regParams Vs Vb K q)\n'
                '    (hm : (m0 + @OM@) %% 4 = 0) (hVb : 18 ≤ Vb) (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) :\n'
                '    %s = %s ∪ %s := by\n'
                '  rw [diagW_add hv @SN@ _ (m0 + %d) (by omega) (by simp only [@SN@]; omega)\n'
                '    (by simp only [@SN@]; omega)]\n'
                '  congr 1\n'
                '  rw [show %s - (((m0 + %d) / 4 : ℕ) : ℤ) = %d by ring]\n'
                '  simp only [Salvo.at, @SN@]\n'
                '  rw [@SD@, translate_translate, translate_ofRows, %s]\n  norm_num\n'
                % (name, gq2, gq, sa, self.oM, self.eP(), self.oM, self.e0, sa))
            special = name
        for e, c in list(A):
            if c is None:
                assert (e, None) in B, ('unmatched generic atom', j, e)
        self._glue_core(j, A, B, special)

    def _glue_core(self, j, A, B, special):
        P = self.P
        A, B = list(A), list(B)
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
        com = ['(%s)' % e if (e.startswith('conway') or ' ' in e) else e for e in common]
        L = ' ∪ '.join(lg + com)
        R = ' ∪ '.join(rg + com)
        unf = ['%sL%d' % (P, j), '%sL%d' % (P, j + 1)] + ['%sG%d' % (P, i) for i in range(len(self.pg))]
        body = ('  simp only [%s, Proc.stop_cons, Proc.start_cons, Proc.stop_nil, Proc.start_nil,\n'
                '    Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty]\n' % ', '.join(unf))
        sp = ('%s q K Vs Vb m0 hv hm hVb hVs' % special) if special else None
        last = ('by rw [%s]; ac_rfl' % sp) if special else 'by ac_rfl'
        if eqs:
            body += ('  calc _ = %s := by ac_rfl\n    _ = %s := by rw [%s]\n    _ = _ := %s\n'
                     % (L, R, ', '.join(eqs), last))
        else:
            body += ('  all_goals ac_rfl\n' if not special else '  rw [%s]\n  all_goals ac_rfl\n' % sp)
        self.gluelem.append('set_option maxRecDepth 100000 in\n/-- The end of segment %d is the start of segment %d. -/\n'
                            'theorem %sGl%d (q : List (Salvo × ℤ)) (K Vs Vb Vs\' : ℤ) (m0 : ℕ)\n'
                            '    (hv : DiagValid regParams Vs Vb K q)\n'
                            '    (hv\' : DiagValid regParams Vs\' Vb K (q ++ [(@SN@, %s)]))\n'
                            '    (hm : (m0 + @OM@) %% 4 = 0) (hVb : 18 ≤ Vb) (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ)) :\n'
                            '    Proc.stop (%sL%d q K Vs Vb Vs\' m0 hv hv\') = Proc.start (%sL%d q K Vs Vb Vs\' m0 hv hv\') := by\n%s'
                            % (j, j + 1, P, j, self.eP(), P, j, P, j + 1, body))

    # ---------------------------------------------------------------- run
    def run(self):
        P = self.P
        segs = self.plan['segs']
        self._phases, self._still, self._flyer = set(), set(), set()
        self.lemmas, self.seglem, self.gluelem = [], [], []
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
        hyps = 'hv hv\' hm hVb hVs hVs\''
        rws = ['(%sSeg0 q K Vs Vb Vs\' m0 %s).evolve_eq' % (P, hyps)]
        for j in range(1, S):
            rws += ['%sGl%d q K Vs Vb Vs\' m0 hv hv\' hm hVb hVs' % (P, j - 1),
                    '(%sSeg%d q K Vs Vb Vs\' m0 %s).evolve_eq' % (P, j, hyps)]
        final = ('set_option maxRecDepth 100000 in\n/-- **The run with the register diagonal**: %d generations, %d segments. -/\n'
                 'theorem %sRun (q : List (Salvo × ℤ)) (K Vs Vb Vs\' : ℤ) (m0 : ℕ)\n'
                 '    (hv : DiagValid regParams Vs Vb K q)\n'
                 '    (hv\' : DiagValid regParams Vs\' Vb K (q ++ [(@SN@, %s)]))\n'
                 '    (hm : (m0 + @OM@) %% 4 = 0) (hVb : 18 ≤ Vb) (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ))\n'
                 '    (hVs\' : -34 ≤ Vs\' + 2 * (((m0 + %d) / 4 : ℕ) : ℤ)) :\n'
                 '    conway.evolve %d (Proc.start (%sL0 q K Vs Vb Vs\' m0 hv hv\')) =\n'
                 '      Proc.stop (%sL%d q K Vs Vb Vs\' m0 hv hv\') := by\n'
                 '  rw [show %d = %s by norm_num]\n  rw [%s]\n  rw [%s]\n'
                 % (tot, S, P, self.eP(), self.oM, tot, P, P, S - 1, tot, expr,
                    ', '.join(['Rule.evolve_add'] * (S - 1)) if S > 1 else 'Rule.evolve_zero',
                    ',\n    '.join(rws)))
        final += '\n' + self.summary_d(segs, tot)
        return chunks, final

    def summary_d(self, segs, tot):
        P = self.P
        first, last = segs[0], segs[-1]
        def others(seg, key):
            out = []
            for p in seg['procs']:
                if p['kind'] in ('cert', 'flight', 'still') and p['start'] and not (seg is last and is_salvo(p)):
                    c = p[key] if p['kind'] != 'still' else p['start']
                    if c:
                        out.append((self.atom(c), c))
            return out
        st, en = others(first, 'start'), others(last, 'stop')
        rest = ' ∪ ('.join('%sR%d' % (P, i) for i in range(len(self.pg))) + ')' * (len(self.pg) - 1)
        unfG = ', '.join('%sG%d' % (P, i) for i in range(len(self.pg)))
        unfA = ', '.join(sorted(set(a for a, _ in st + en)))
        lhs = ' ∪ '.join(ofrows(c) for _, c in st)
        rhs = ' ∪ '.join(ofrows(c) for _, c in en)
        rhs = (rhs + ' ∪ ') if rhs else ''
        q2 = '(q ++ [(@SN@, %s)])' % self.eP()
        return ('/-- The register circuit at rest at the reference time. -/\ndef %sRest : Finset Cell :=\n  %s\n\n'
                'set_option maxRecDepth 100000 in\n'
                '/-- **An operation of the register with the register diagonal**: the circuit at rest, its control\n'
                'glider and the register diagonal (block `K`, salvos `q` in flight, every block at position\n'
                '`≥ 0`) evolve in %d generations into the circuit at rest, the answer (if any), and the\n'
                'diagonal with the new salvo added. -/\n'
                'theorem %sOp (q : List (Salvo × ℤ)) (K Vs Vb Vs\' : ℤ) (m0 : ℕ)\n'
                '    (hv : DiagValid regParams Vs Vb K q)\n'
                '    (hv\' : DiagValid regParams Vs\' Vb K %s)\n'
                '    (hm : (m0 + @OM@) %% 4 = 0) (hVb : 18 ≤ Vb) (hVs : 18 ≤ Vs + 2 * ((m0 / 4 : ℕ) : ℤ))\n'
                '    (hVs\' : -34 ≤ Vs\' + 2 * (((m0 + @OM@) / 4 : ℕ) : ℤ)) :\n'
                '    conway.evolve %d (%sRest ∪ %s ∪ conway.evolve m0 (diagW q K)) =\n'
                '      %sRest ∪ %sconway.evolve (m0 + %d) (diagW %s K) := by\n'
                '  have h := %sRun q K Vs Vb Vs\' m0 hv hv\' hm hVb hVs hVs\'\n'
                '  simp only [%sL0, %sL%d, %s, %s, Proc.stop_cons, Proc.start_cons, Proc.stop_nil,\n'
                '    Proc.start_nil, Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty,\n'
                '    Rule.evolve_zero, add_zero] at h\n'
                '  rw [%sRest]\n'
                '  refine (congrArg (conway.evolve %d) ?_).trans (h.trans ?_) <;> ac_rfl\n'
                % (P, rest, tot, P, q2, tot, P, lhs, P, rhs, tot, q2, P, P, P, len(segs) - 1, unfG, unfA, P, tot))


def cells_of(x0, y0, rows):
    out = set()
    for i, r in enumerate(rows):
        j = 0
        while r:
            if r & 1:
                out.add((x0 + j, y0 + i))
            r >>= 1
            j += 1
    return out


def main():
    plan_path, prefix, moddir, merge = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    per = int(sys.argv[5]) if len(sys.argv) > 5 else 8
    kind = sys.argv[6] if len(sys.argv) > 6 else 'pull'
    phase = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    plan = pickle.load(open(plan_path, 'rb'))
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'life_machine'))
    from net import piece_cells
    em = DiagEmitter(plan, prefix, merge, kind, phase)
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
    doc = ('# Generated certificate `%s`: %s\n\nGenerated by `scripts/life_cert/emit_diag.py` from a segment\n'
           'plan (`scripts/life_cert/plan.py`); the generator is untrusted, Lean checks every step.')
    opts = 'set_option linter.style.longLine false\nset_option linter.unusedVariables false\n\n'
    with open(os.path.join(moddir, Cap + 'Data.lean'), 'w') as f:
        f.write(HEADER % ('public import LeanTheory.Theory.Life.DiagProc\npublic import LeanTheory.Theory.Life.SalvoPhases',
                          doc % (prefix, 'the pieces and configurations')))
        f.write(opts)
        f.write('\n'.join(pieces_txt + em.atom_defs + em.lemmas).replace('@OM@', str(em.oM)).replace('@SN@', em.SN).replace('@SD@', em.SD))
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
            f.write('\n'.join(em.seglem[lo:hi]).replace('@OM@', str(em.oM)).replace('@SN@', em.SN).replace('@SD@', em.SD))
            f.write(FOOTER)
    with open(os.path.join(moddir, Cap + 'Run.lean'), 'w') as f:
        f.write(HEADER % ('\n'.join('public import %s%s' % (base, nm) for nm in files),
                          doc % (prefix, 'the glue and the whole run')))
        f.write('set_option linter.style.longLine false\nset_option linter.unusedSimpArgs false\n'
                'set_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n'
                'set_option linter.unusedVariables false\n\n')
        f.write('\n'.join(em.gluelem + [final]).replace('@OM@', str(em.oM)).replace('@SN@', em.SN).replace('@SD@', em.SD))
        f.write(FOOTER)
    print('segments', len(chunks), 'atoms', len(em.atoms), 'merge segment', em.jM, 'offset', em.e0, 'files', files)


if __name__ == '__main__':
    main()
