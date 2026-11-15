#!/usr/bin/env python3
"""Lean emitter for a segment plan (see plan.py): writes the certificate of a circuit run as a
chain of segments, each a list of processes (local certificates, flights, still lifes, and one
bundle of idle pieces), glued at the boundaries.  Untrusted generator: Lean checks everything.

Usage: emit.py PLAN.pkl PREFIX MODULEDIR [SEGS_PER_FILE]
  writes MODULEDIR/<Prefix>Data.lean, <Prefix>Seg<i>.lean, <Prefix>Run.lean."""
import os
import pickle
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'life_gates'))
from life import window_of_cells, step_cells  # noqa: E402

HEADER = """/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

%s

/-!
%s
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

"""
FOOTER = "\nend LeanTheory.Life\n"


def z(v):
    return '(%d)' % v if v < 0 else '%d' % v


def ofrows(cells):
    x0, y0, rows = window_of_cells(cells)
    return 'ofRows %s %s [%s]' % (z(x0), z(y0), ', '.join(str(r) for r in rows))


def ofrows_ml(cells, ind='    '):
    """ofRows on several lines (one row per line when long)."""
    x0, y0, rows = window_of_cells(cells)
    s = 'ofRows %s %s [%s]' % (z(x0), z(y0), ', '.join(str(r) for r in rows))
    if len(ind) + len(s) <= 98:
        return s
    out = 'ofRows %s %s\n%s  [' % (z(x0), z(y0), ind)
    line = ''
    parts = []
    for r in rows:
        t = str(r)
        if len(ind) + 3 + len(line) + len(t) + 2 > 98 and line:
            parts.append(line)
            line = ''
        line += t + ', '
    parts.append(line)
    parts[-1] = parts[-1][:-2] + ']'
    return out + ('\n%s   ' % ind).join(p.rstrip() for p in parts)


def box(b):
    return 'Box %s %s %s %s' % (z(b[0]), z(b[2]), z(b[1]), z(b[3]))


def far_disj(b1, b2):
    """The disjunct of `Box.farApart` (r = 2) that holds for static boxes, as an `Or` proof."""
    conds = [b1[2] + 2 < b2[0], b2[2] + 2 < b1[0], b1[3] + 2 < b2[1], b2[3] + 2 < b1[1]]
    k = conds.index(True)
    return ['Or.inl (by norm_num)', 'Or.inr (Or.inl (by norm_num))',
            'Or.inr (Or.inr (Or.inl (by norm_num)))', 'Or.inr (Or.inr (Or.inr (by norm_num)))'][k]


def evolve(cells, n):
    for _ in range(n):
        cells = step_cells(cells)
    return cells


class Emitter:
    def __init__(self, plan, prefix):
        self.plan = plan
        self.P = prefix
        self.atoms = {}            # frozenset(cells) -> name
        self.atom_defs = []
        self.lemmas = []           # data-file lemmas (atoms' properties)
        self.groups = plan['groups']
        self.pg = [g for g in self.groups if g[1] == 'piece']
        self.gi = {g[0]: i for i, g in enumerate(self.pg)}

    # ---------------------------------------------------------------- atoms
    def atom(self, cells):
        key = frozenset(cells)
        if key not in self.atoms:
            name = '%sA%d' % (self.P, len(self.atoms))
            self.atoms[key] = name
            self.atom_defs.append('/-- A configuration of the run (generated). -/\ndef %s : Finset Cell :=\n  %s\n'
                                  % (name, ofrows_ml(cells, '  ')))
        return self.atoms[key]

    # ---------------------------------------------------------------- pieces
    def piece_defs(self, rest_at_Ts):
        out = []
        for i, g in enumerate(self.pg):
            name, kind, env, members = g
            cells = rest_at_Ts[name]
            out.append('/-- Group `%s` of the circuit at rest at the reference time (pieces %s). -/\n'
                       'def %sR%d : Finset Cell :=\n  %s\n' % (name, members, self.P, i, ofrows_ml(cells, '  ')))
            out.append('/-- **Certificate**: group `%s` has period 30 and stays in its box. -/\n'
                       'theorem %sR%d_rest : Reaction %sR%d %sR%d 30 (fun _ => %s) := by\n'
                       '  rw [%sR%d]\n  life_reaction\n' % (name, self.P, i, self.P, i, self.P, i, box(env),
                                                          self.P, i))
            out.append('/-- Group `%s` as a piece. -/\ndef %sG%d : Piece :=\n  ⟨%sR%d, %s, %s, %s, %s, %sR%d_rest⟩\n'
                       % (name, self.P, i, self.P, i, z(env[0]), z(env[2]), z(env[1]), z(env[3]), self.P, i))
        names = ', '.join('%sG%d' % (self.P, i) for i in range(len(self.pg)))
        out.append('/-- All groups of the circuit. -/\ndef %sPieces : List Piece := [%s]\n' % (self.P, names))
        # global separation
        parts = []
        for x in range(len(self.pg)):
            hs = []
            for y in range(x + 1, len(self.pg)):
                bx, by = self.pg[x][2], self.pg[y][2]
                hs.append('(Box.farApart (%s) : FarApart 2 (%s) (%s))' % (far_disj(bx, by), box(bx), box(by)))
            parts.append('⟨' + ', '.join(hs + ['trivial']) + '⟩' if hs else 'trivial')
        out.append('/-- The groups at rest are pairwise far apart. -/\n'
                   'theorem %sPieces_sep : %sPieces.Pairwise Piece.Sep :=\n  PairR.pairwise\n    %s\n'
                   % (self.P, self.P, self.nest(parts, '    ')))
        return out

    def nest(self, parts, ind):
        """⟨p0, ⟨p1, ... ⟨pk, trivial⟩⟩⟩ for PairR."""
        s = 'trivial'
        for p in reversed(parts):
            s = '⟨%s,\n%s %s⟩' % (p, ind, s)
        return s

    # ---------------------------------------------------------------- phases
    def phase_lemma(self, i, s, cells):
        name = '%sR%d_ph%d' % (self.P, i, s)
        if name not in self._phases:
            self._phases.add(name)
            if s == 0:
                pf = '  rfl'
            else:
                pf = '  rw [%sR%d]\n  life_cert' % (self.P, i)
            self.lemmas.append('/-- Group %d at phase %d. -/\ntheorem %s :\n    conway.evolve %d %sR%d =\n      %s := by\n%s\n'
                               % (i, s, name, s, self.P, i, ofrows_ml(cells, '      '), pf))
        return name

    # ---------------------------------------------------------------- movers
    def fp(self, p, iv):
        """Footprint of a mover at generation `iv` (a Lean expression)."""
        if p['kind'] == 'flight':
            (dx, dy), pb = p['v'], p['pb']
            q = '((%s / 4 : ℕ) : ℤ)' % iv
            return 'Box (%s + %s * %s) (%s + %s * %s) (%s + %s * %s) (%s + %s * %s)' % (
                z(pb[0]), q, z(dx), z(pb[2]), q, z(dx), z(pb[1]), q, z(dy), z(pb[3]), q, z(dy))
        return box(p['box'])

    def mover(self, j, m, p, n):
        """Lemmas for mover m of segment j; returns the Lean `Proc n` literal."""
        P = self.P
        A = self.atom(p['start'])
        if p['kind'] == 'cert':
            B = self.atom(p['stop'])
            name = '%sC%d_%d' % (P, j, m)
            unf = A if A == B else '%s, %s' % (A, B)
            self.seglem.append('set_option maxRecDepth 100000 in\n/-- **Certificate** (segment %d, process %d). -/\n'
                               'theorem %s : Reaction %s %s %d (fun _ => %s) := by\n  rw [%s]\n  life_reaction\n'
                               % (j, m, name, A, B, n, box(p['box']), unf))
            return '{ P := %s, Q := %s, F := fun _ => %s, reaction := %s }' % (A, B, box(p['box']), name)
        if p['kind'] == 'still':
            if A not in self._still:
                self._still.add(A)
                self.lemmas.append('/-- A still life of the run. -/\ntheorem %s_still : IsStillLife %s := by\n'
                                   '  rw [%s]\n  exact ⟨ofRows_nonempty rfl _ _, by rw [← Rule.evolve_one]; life_cert⟩\n'
                                   % (A, A, A))
                self.lemmas.append('/-- The still life in its box. -/\ntheorem %s_sub : (%s : Set Cell) ⊆ %s := by\n'
                                   '  rw [%s]\n  exact coe_ofRows_subset_box rfl\n' % (A, A, box(p['box']), A))
            return ('{ P := %s, Q := %s, F := fun _ => %s, reaction := %s_still.reaction_box %s_sub %d }'
                    % (A, A, box(p['box']), A, A, n))
        # flight
        B = self.atom(p['stop'])
        (dx, dy), pb = p['v'], p['pb']
        if A not in self._flyer:
            self._flyer.add(A)
            self.lemmas.append('/-- A flying object of the run moves by `(%d, %d)` every four generations. -/\n'
                               'theorem %s_four : conway.evolve 4 %s = translate (%s, %s) %s := by\n'
                               '  rw [%s, translate_ofRows]\n  life_cert\n' % (dx, dy, A, A, z(dx), z(dy), A, A))
            self.lemmas.append('/-- During its first four generations the object stays in a box. -/\n'
                               'theorem %s_box (r : ℕ) (hr : r < 4) :\n    (conway.evolve r %s : Set Cell) ⊆ %s := by\n'
                               '  interval_cases r <;> (rw [%s]; life_eval; exact coe_ofRows_subset_box rfl)\n'
                               % (A, A, box(pb), A))
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
        self.seglem.append('/-- A flight (segment %d, process %d). -/\ntheorem %s :\n    Reaction %s %s %d (fun i => %s) :=\n'
                           '  flight_reaction %s_four %s_box %d %d %se\n'
                           % (j, m, name, A, B, n, self.fp(p, 'i'), A, A, q, r, name))
        return '{ P := %s, Q := %s, F := fun i => %s, reaction := %s }' % (A, B, self.fp(p, 'i'), name)

    def indep(self, p, q):
        if p['kind'] != 'flight' and q['kind'] != 'flight':
            return '(fun _ _ => (Box.farApart (%s) : FarApart 2 (%s) (%s)))' % (
                far_disj(p['box'], q['box']), box(p['box']), box(q['box']))
        return '(fun i _hi => (Box.farApart (by omega) : FarApart 2 (%s) (%s)))' % (
            self.fp(p, 'i'), self.fp(q, 'i'))

    def indep_bundle(self, p, idle):
        terms = []
        for gi in idle:
            env = self.pg[gi][2]
            if p['kind'] != 'flight':
                terms.append('(fun _ _ => (Box.farApart (%s) : FarApart 2 (%s) (%s)))'
                             % (far_disj(p['box'], env), box(p['box']), box(env)))
            else:
                terms.append('(fun i _hi => (Box.farApart (by omega) : FarApart 2 (%s) (%s)))'
                             % (self.fp(p, 'i'), box(env)))
        if not terms:
            return 'Piece.indep_bundle _ _ _ _ _ _ trivial'
        return 'Piece.indep_bundle _ _ _ _ _ _\n        ⟨' + ',\n         '.join(terms + ['trivial']) + '⟩'

    # ---------------------------------------------------------------- segments
    def segment(self, j, seg):
        P = self.P
        Ts = self.plan['Ts']
        a, b = seg['a'], seg['b']
        n = b - a
        s, s2 = (a - Ts) % 30, (b - Ts) % 30
        movers = [p for p in seg['procs'] if p['kind'] in ('cert', 'flight', 'still') and p['start']]
        idle = sorted(self.gi[p['group']] for p in seg['procs'] if p['kind'] == 'idle')
        lits = [self.mover(j, m, p, n) for m, p in enumerate(movers)]
        # the bundle
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
        self.seglem.append('/-- The processes of segment %d (generations %d to %d of the run). -/\n'
                           'def %sL%d : List (Proc %d) :=\n  [%s]\n' % (j, a, b, P, j, n, ',\n   '.join(lits + [bundle])))
        parts = []
        for x, p in enumerate(movers):
            terms = [self.indep(p, q) for q in movers[x + 1:]] + [self.indep_bundle(p, idle)]
            parts.append('⟨' + ',\n      '.join(terms + ['trivial']) + '⟩')
        parts.append('trivial')
        self.seglem.append('set_option maxRecDepth 100000 in\n/-- **Segment %d** of the run: its processes side by side. -/\n'
                           'theorem %sSeg%d : Reaction (Proc.start %sL%d) (Proc.stop %sL%d) %d (Proc.foot %sL%d) :=\n'
                           '  Reaction.parList _ (PairR.pairwise\n    %s)\n'
                           % (j, P, j, P, j, P, j, n, P, j, self.nest(parts, '    ')))
        # atoms at both ends, for the glue
        start = [(self.atom(p['start']), set(p['start'])) for p in movers]
        start += [('conway.evolve %d %sR%d' % (s, P, i), self.rest_cells(i, a)) for i in idle]
        stop = [(self.atom(p['stop'] if p['kind'] != 'still' else p['start']),
                 set(p['stop'] if p['kind'] != 'still' else p['start'])) for p in movers]
        stop += [('conway.evolve %d %sR%d' % (s2, P, i), self.rest_cells(i, b)) for i in idle]
        return start, stop

    def rest_cells(self, i, t):
        return self.rest[(self.pg[i][0], (t - self.plan['Ts']) % 30)]

    # ---------------------------------------------------------------- glue
    def unfold(self, e):
        """Rewrite rule turning an atom expression into its `ofRows`."""
        if e.startswith('conway.evolve'):
            _, s, r = e.split()
            i = int(r[len(self.P) + 1:])
            return self.phase_lemma(i, int(s), self.rest_cells_phase(i, int(s)))
        return e

    def union_to(self, atoms, Zcells, name, doc):
        """Lemma `name : a1 ∪ ... ∪ ak = ofRows Z` (k >= 1)."""
        Zx, Zy, _ = window_of_cells(Zcells)
        lhs = ' ∪ '.join(e if not e.startswith('conway') else '(%s)' % e for e, _ in atoms)
        rws = [self.unfold(e) for e, _ in atoms]
        lines = ['  rw [%s]' % ', '.join(rws)]
        if len(atoms) > 1:
            pads = []
            for e, c in atoms:
                x, y, rows = window_of_cells(c)
                pads.append("ofRows_eq_padRows' %s %s %s %s %d %d _ (by norm_num) (by norm_num)"
                            % (z(Zx), z(Zy), z(x), z(y), y - Zy, x - Zx))
            lines.append('  rw [%s]' % ',\n    '.join(pads))
            lines.append('  rw [%s]' % ', '.join(['← ofRows_orRows'] * (len(atoms) - 1)))
            lines.append('  rfl')
        self.gluelem.append('set_option maxRecDepth 100000 in\n/-- %s -/\ntheorem %s :\n    %s =\n      %s := by\n%s\n'
                            % (doc, name, lhs, ofrows_ml(Zcells, '      '), '\n'.join(lines)))

    def glue(self, j, stop, start):
        """`Proc.stop L_j = Proc.start L_{j+1}`."""
        P = self.P
        A = list(stop)
        B = list(start)
        common = []
        for e, c in list(A):
            for k, (e2, c2) in enumerate(B):
                if e2 == e:
                    common.append(e)
                    A.remove((e, c))
                    del B[k]
                    break
        # clusters of the remaining atoms by overlapping cells
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
        eqs = []
        lgroups, rgroups = [], []
        for ci, mem in enumerate(cl.values()):
            ea = [(e, c) for s_, e, c in mem if s_ == 'A']
            eb = [(e, c) for s_, e, c in mem if s_ == 'B']
            ua = set().union(*[c for _, c in ea]) if ea else set()
            ub = set().union(*[c for _, c in eb]) if eb else set()
            if ua != ub or not ea or not eb:
                raise ValueError(('glue mismatch', j, [e for e, _ in ea], [e for e, _ in eb]))
            za = '%sZ%d_%da' % (P, j, ci)
            zb = '%sZ%d_%db' % (P, j, ci)
            self.union_to(ea, ua, za, 'Glue %d, cluster %d, before.' % (j, ci))
            self.union_to(eb, ub, zb, 'Glue %d, cluster %d, after.' % (j, ci))
            eqs.append('%s, ← %s' % (za, zb))
            par_e = lambda es: '(' + ' ∪ '.join(e if not e.startswith('conway') else '(%s)' % e for e, _ in es) + ')'
            lgroups.append(par_e(ea))
            rgroups.append(par_e(eb))
        com = ['(%s)' % e if e.startswith('conway') else e for e in common]
        L = ' ∪ '.join(lgroups + com) if (lgroups + com) else '∅'
        R = ' ∪ '.join(rgroups + com) if (rgroups + com) else '∅'
        unf = ['%sL%d' % (P, j), '%sL%d' % (P, j + 1)] + ['%sG%d' % (P, i) for i in range(len(self.pg))]
        body = ('  simp only [%s, Proc.stop_cons, Proc.start_cons, Proc.stop_nil, Proc.start_nil,\n'
                '    Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty]\n' % ', '.join(unf))
        if eqs:
            body += ('  calc _ = %s := by ac_rfl\n    _ = %s := by rw [%s]\n    _ = _ := by ac_rfl\n'
                     % (L, R, ', '.join(eqs)))
        else:
            body += '  all_goals ac_rfl\n'
        self.gluelem.append('set_option maxRecDepth 100000 in\n/-- The end of segment %d is the start of segment %d. -/\n'
                            'theorem %sGl%d : Proc.stop %sL%d = Proc.start %sL%d := by\n%s'
                            % (j, j + 1, P, j, P, j, P, j + 1, body))

    def summary(self):
        """The run stated with the circuit at rest and the other configurations written out."""
        P = self.P
        segs = self.plan['segs']
        Ts = self.plan['Ts']
        tot = sum(seg['b'] - seg['a'] for seg in segs)
        first, last = segs[0], segs[-1]
        assert (first['a'] - Ts) % 30 == 0 and (last['b'] - Ts) % 30 == 0
        def others(seg, key):
            out = []
            for p in seg['procs']:
                if p['kind'] in ('cert', 'flight', 'still') and p['start']:
                    c = p[key] if p['kind'] != 'still' else p['start']
                    if c:
                        out.append((self.atom(c), c))
            return out
        st, en = others(first, 'start'), others(last, 'stop')
        rest = ' ∪ '.join('%sR%d' % (P, i) for i in range(len(self.pg)))
        idle0 = [p for p in first['procs'] if p['kind'] == 'idle']
        idle1 = [p for p in last['procs'] if p['kind'] == 'idle']
        assert len(idle0) == len(self.pg) and len(idle1) == len(self.pg)
        lhs = '(%sRest ∪ %s)' % (P, ' ∪ '.join(ofrows(c) for _, c in st))
        rhs = '%sRest ∪ %s' % (P, ' ∪ '.join(ofrows(c) for _, c in en))
        unf = ['%sL0' % P, '%sL%d' % (P, len(segs) - 1)] + ['%sG%d' % (P, i) for i in range(len(self.pg))]
        unf += sorted(set(a for a, _ in st + en))
        return ('/-- The whole circuit at rest at the reference time. -/\ndef %sRest : Finset Cell :=\n  %s\n\n'
                'set_option maxRecDepth 100000 in\n/-- **The run of the circuit**, stated with the circuit at rest. -/\n'
                'theorem %sRun_rest :\n    conway.evolve %d\n      %s =\n      %s := by\n'
                '  have h := %sRun\n'
                '  simp only [%s, Proc.stop_cons, Proc.start_cons, Proc.stop_nil, Proc.start_nil,\n'
                '    Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty, Rule.evolve_zero] at h\n'
                '  rw [%sRest]\n  refine (congrArg (conway.evolve %d) ?_).trans (h.trans ?_) <;> ac_rfl\n'
                % (P, rest, P, tot, lhs, rhs, P, ', '.join(unf), P, tot))

    def rest_cells_phase(self, i, s):
        return self.rest[(self.pg[i][0], s)]

    # ---------------------------------------------------------------- run
    def run(self):
        P = self.P
        segs = self.plan['segs']
        self._phases, self._still, self._flyer = set(), set(), set()
        self.lemmas, self.seglem, self.gluelem = [], [], []
        ends = []
        seg_chunks = []
        for j, seg in enumerate(segs):
            mark = len(self.seglem)
            ends.append(self.segment(j, seg))
            seg_chunks.append((mark, len(self.seglem)))
        for j in range(len(segs) - 1):
            self.glue(j, ends[j][1], ends[j + 1][0])
        ns = [seg['b'] - seg['a'] for seg in segs]
        S = len(segs)
        tot = sum(ns)
        expr = str(ns[0])
        for x in ns[1:]:
            expr = '%d + (%s)' % (x, expr)
        rws = ['%sSeg0.evolve_eq' % P]
        for j in range(1, S):
            rws += ['%sGl%d' % (P, j - 1), '%sSeg%d.evolve_eq' % (P, j)]
        final = ('set_option maxRecDepth 100000 in\n/-- **The run**: %d generations, %d segments. -/\n'
                 'theorem %sRun : conway.evolve %d (Proc.start %sL0) = Proc.stop %sL%d := by\n'
                 '  rw [show %d = %s by norm_num]\n  rw [%s]\n  rw [%s]\n'
                 % (tot, S, P, tot, P, P, S - 1, tot, expr,
                    ', '.join(['Rule.evolve_add'] * (S - 1)) if S > 1 else 'Rule.evolve_zero',
                    ',\n    '.join(rws)))
        return seg_chunks, final


def main():
    plan_path, prefix, moddir = sys.argv[1], sys.argv[2], sys.argv[3]
    per = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    plan = pickle.load(open(plan_path, 'rb'))
    sys.path.insert(0, os.path.join(HERE, '..', 'life_machine'))
    from net import piece_cells
    em = Emitter(plan, prefix)
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
    doc = ('# Generated certificate `%s`: %s\n\nGenerated by `scripts/life_cert/emit.py` from a segment\n'
           'plan (`scripts/life_cert/plan.py`); the generator is untrusted, Lean checks every step.')
    with open(os.path.join(moddir, Cap + 'Data.lean'), 'w') as f:
        f.write(HEADER % ('public import LeanTheory.Theory.Life.Network', doc % (prefix, 'the pieces and configurations')))
        f.write('set_option linter.style.longLine false\n\n')
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
            f.write('set_option linter.style.longLine false\n\n')
            f.write('\n'.join(em.seglem[lo:hi]))
            f.write(FOOTER)
    with open(os.path.join(moddir, Cap + 'Run.lean'), 'w') as f:
        f.write(HEADER % ('\n'.join('public import %s%s' % (base, nm) for nm in files),
                          doc % (prefix, 'the glue and the whole run')))
        f.write('set_option linter.style.longLine false\nset_option linter.unusedSimpArgs false\n'
                'set_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n\n')
        f.write('\n'.join(em.gluelem + [final, em.summary()]))
        f.write(FOOTER)
    print('segments', len(chunks), 'atoms', len(em.atoms), 'files', files)


if __name__ == '__main__':
    main()
