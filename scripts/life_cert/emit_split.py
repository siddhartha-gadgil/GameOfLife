#!/usr/bin/env python3
"""Emit `<Prefix>Split.lean`: a generated run with its answer glider split off (research note N-22).

From the cut segment `K0` on, the answer glider of the run is a lone flight (one process per
segment, each a flight from the end of the previous one). The file states

* `<p>PreS`: the run up to the cut, inside `<p>Region`, ending at `Proc.start <p>LrestS ∪ A`
  (`A` the answer glider);
* `<p>RestS`: the rest of the run (the circuit finishing, with the register diagonal) on its
  own, inside `<p>RestRegion` (a union of components and `regLanes`);
* `<p>AnsS`: the flight of the answer glider, inside a moving box far from `<p>RestRegion`;
* `<final>S`: the operation as the prefix, then the rest and the answer side by side.

Generated from the generated segment files; untrusted, Lean checks every step.

Usage: emit_split.py PREFIX K0 ANS_U1 ANS_U2 [ANS_V1 ANS_V2]
  (the answer process of a segment is the flight whose component lies in the given u-range, or
  in the given v-range when that is given)
"""
import glob
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import emit_rung as E  # noqa: E402

GEN = E.GEN
SLACK = 2


def main():
    p = sys.argv[1]
    P = p[0].upper() + p[1:]
    K0 = int(sys.argv[2])
    au1, au2 = int(sys.argv[3]), int(sys.argv[4])
    vr = (int(sys.argv[5]), int(sys.argv[6])) if len(sys.argv) > 6 else None
    data = E.read(os.path.join(GEN, P + 'Data.lean'))
    pieces = {}
    for m in re.finditer(r'def (' + p + r'G\d+) : Piece :=\s*⟨\w+, ' + ', '.join([E.NUM] * 4),
                         data):
        pieces[m.group(1)] = tuple(map(int, m.groups()[1:]))
    segs = {}
    for f in glob.glob(os.path.join(GEN, P + 'Seg*.lean')):
        txt = E.read(f)
        for m in re.finditer(r'def (' + p + r'L(\d+))(.*?):\s*List \(Proc (\d+)\) :=\s*\n', txt,
                             re.S):
            k = int(m.group(2))
            st = txt.index('[', m.end())
            body = txt[st + 1:E.match_close(txt, st)]
            hm = re.search(r'theorem ' + p + 'Seg' + str(k) + r'\b(.*?):\s*\n?\s*Reaction', txt,
                           re.S)
            segs[k] = dict(binders=m.group(3), n=int(m.group(4)), procs=E.split_top(body),
                           sbinders=hm.group(1) if hm else '')
    last = max(segs)
    run = E.read(os.path.join(GEN, P + 'Run.lean'))
    rung = E.read(os.path.join(GEN, P + 'RunG.lean'))
    diag = 'regLanes' in re.search(r'def ' + p + r'RegL.*?\]\n', rung, re.S).group(0)

    def lnames(bt):
        out, j = [], 0
        while j < len(bt):
            if bt[j] == '(':
                e = E.match_close(bt, j)
                out += bt[j + 1:e].split(':')[0].split()
                j = e + 1
            else:
                j += 1
        return out

    def fx_of(pr):
        return re.search(r'F := (.*?),\s*reaction :=', pr, re.S).group(1)

    def is_ans(pr, n):
        if pr.startswith('Piece.bundle'):
            return False
        c = E.comp_of(fx_of(pr), n)
        if c is None or c[8] == 'box':
            return False
        if vr:
            return vr[0] <= c[6] and c[7] <= vr[1]
        return au1 <= c[4] and c[5] <= au2

    # answer processes of the tail
    ans = {}
    for k in range(K0, last + 1):
        idx = [i for i, pr in enumerate(segs[k]['procs']) if is_ans(pr, segs[k]['n'])]
        assert len(idx) == 1, (k, idx)
        ans[k] = idx[0]
    offs, o = {}, 0
    for k in range(K0, last + 1):
        offs[k] = o
        o += segs[k]['n']
    Ttail = o

    def pq(pr):
        m = re.search(r'P := (.*?), Q := (.*?), F', pr, re.S)
        return m.group(1).strip(), m.group(2).strip()

    def rx(pr):
        return re.search(r'reaction := (\w+)', pr).group(1)

    A0 = pq(segs[K0]['procs'][ans[K0]])[0]
    Alast = pq(segs[last]['procs'][ans[last]])[1]
    for k in range(K0, last):
        assert pq(segs[k]['procs'][ans[k]])[1] == pq(segs[k + 1]['procs'][ans[k + 1]])[0], k
    # the moving box of the answer, from its first process, with slack
    fx0 = fx_of(segs[K0]['procs'][ans[K0]])
    mb = re.match(r'fun i => Box ' + ' '.join([E.MOV] * 4), fx0)
    g = list(map(int, mb.groups()))
    (a0, dx), (b0, _), (l0, dy), (h0, _) = [(g[2 * k], g[2 * k + 1]) for k in range(4)]
    a0, b0, l0, h0 = a0 - SLACK, b0 + SLACK, l0 - SLACK, h0 + SLACK

    def fa(t):
        return (f'Box ({a0} + (({t} / 4 : ℕ) : ℤ) * ({dx})) ({b0} + (({t} / 4 : ℕ) : ℤ) * ({dx})) '
                f'({l0} + (({t} / 4 : ℕ) : ℤ) * ({dy})) ({h0} + (({t} / 4 : ℕ) : ℤ) * ({dy}))')
    # numerical check of the slack
    for k in range(K0, last + 1):
        fxk = fx_of(segs[k]['procs'][ans[k]])
        mk = re.match(r'fun i => Box ' + ' '.join([E.MOV] * 4), fxk)
        gk = list(map(int, mk.groups()))
        for i in range(segs[k]['n'] + 1):
            t = i + offs[k]
            q, Q = i // 4, t // 4
            assert a0 + Q * dx <= gk[0] + q * gk[1] and gk[2] + q * gk[3] <= b0 + Q * dx, (k, i)
            assert l0 + Q * dy <= gk[4] + q * gk[5] and gk[6] + q * gk[7] <= h0 + Q * dy, (k, i)
    # components of the rest
    comps = []
    for k in range(K0, last + 1):
        s = segs[k]
        for j, pr in enumerate(s['procs']):
            if j == ans[k]:
                continue
            if pr.startswith('Piece.bundle'):
                for x in re.findall(p + r'G\d+', pr[:pr.index(']')]):
                    a, b, lo, hi = pieces[x]
                    comps.append((a, b, lo, hi, a - hi, b - lo, a + lo, b + hi))
            else:
                c = E.comp_of(fx_of(pr), s['n'])
                if c is not None:
                    comps.append(c[:8])
    comps = E.merge_all(comps)
    lanes_idx = len(comps) if diag else None
    regl = [E.bu(c) for c in comps] + (['regLanes'] if diag else [])

    def find(c):
        for k, C in enumerate(comps):
            if E.contains(C, c):
                return k, C
        raise SystemExit('no component for ' + str(c))

    # numerical check: the answer box far from every component, at every time of the tail
    def far(c, B):
        a, b, lo, hi, U1, U2, V1, V2 = c
        a2, b2, lo2, hi2 = B
        return (b + 2 < a2 or b2 + 2 < a or hi + 2 < lo2 or hi2 + 2 < lo or U2 + 4 < a2 - hi2 or
                b2 - lo2 + 4 < U1 or V2 + 4 < a2 + lo2 or b2 + hi2 + 4 < V1)
    for Q in range(Ttail // 4 + 1):
        B = (a0 + Q * dx, b0 + Q * dx, l0 + Q * dy, h0 + Q * dy)
        for c in comps:
            assert far(c, B), ('answer near component', Q, c)
        if diag:
            assert B[1] + B[3] + 4 < 354 or -65 < B[0] - B[3] or B[1] - B[2] + 4 < -113, Q

    def rest_proof(pr, n, wrap):
        """Proof that a non-answer process stays in the rest region (wrapped for `T`)."""
        def W(x):
            return f'Set.subset_union_of_subset_left ({x}) _' if wrap else x
        if pr.startswith('Piece.bundle'):
            names = re.findall(p + r'G\d+', pr[:pr.index(']')])
            bs = []
            for x in names:
                a, b, lo, hi = pieces[x]
                k_, C = find((a, b, lo, hi, a - hi, b - lo, a + lo, b + hi))
                bs.append(f'subset_unionL (X := {E.bu(C)}) ({E.memproof(k_)}) '
                          f'(box_subset_BU (a := {a}) (b := {b}) (lo := {lo}) (hi := {hi}) '
                          f'(by norm_num))')
            return ('fun i _ => ' + W('Piece.bundle_F_subset (L := [' + ', '.join(names) +
                                      ']) ⟨' + ', '.join(bs) + ', trivial⟩ i'))
        fx = fx_of(pr)
        c = E.comp_of(fx, n)
        if 'wStrip' in fx:
            return ('fun i hi => ' + W(f'(wStrip_subset_regLanes (by omega) (by omega)).trans '
                                       f'(subset_unionL (L := {p}RestRegL) '
                                       f'({E.memproof(lanes_idx)}) subset_rfl)'))
        if c is None:
            return ('fun i _ => ' + W(f'subset_unionL (L := {p}RestRegL) '
                                      f'({E.memproof(lanes_idx)}) (fun c hc => by '
                                      f'simp only [Box, regLanes, Set.mem_ofPred_eq] at hc ⊢; '
                                      f'omega)'))
        k_, C = find(c[:8])
        lem = 'boxUV_subset_BU' if c[8] == 'movuv' else 'box_subset_BU'
        tac = 'norm_num' if c[8] == 'box' else 'omega'
        return ('fun i hi => ' + W(f'subset_unionL (X := {E.bu(C)}) ({E.memproof(k_)}) '
                                   f'({lem} (by {tac}))'))

    def ans_proof(pr):
        fx = fx_of(pr)
        core = 'box_subset_of (by omega)'
        if '∩ UVBox' in fx:
            core = f'Set.inter_subset_left.trans ({core})'
        return f'fun i hi => Set.subset_union_of_subset_right (show _ ⊆ {p}AnsF _ from {core}) _'

    import textwrap
    doc = (f'Generated by `scripts/life_cert/emit_split.py`; the generator is untrusted, Lean '
           f'checks every step. From segment {K0} (generation {sum(segs[k]["n"] for k in range(K0))}) '
           f'on, the answer glider `{A0}` flies alone; the rest of the run (the circuit finishing) '
           f'stays in `{p}RestRegion`, and the answer in a moving box far from it.')

    def wrap(t):
        return '\n'.join(textwrap.wrap(t, 100))
    out = [f'''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Gen.{P}RunG
public import LeanTheory.Theory.Life.RunSplit

/-!
# Generated: the run `{p}` with its answer split off

{wrap(doc)}
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The components of the region of the rest of the run `{p}` after the cut. -/
def {p}RestRegL : List (Set Cell) :=
  [{(',' + chr(10) + '   ').join(regl)}]

/-- The region of the rest of the run `{p}` after the cut. -/
def {p}RestRegion : Set Cell := unionL {p}RestRegL

/-- A set far from every component is far from the region of the rest. -/
theorem {p}RestRegion_far {{B : Set Cell}} (h : FarAll B {p}RestRegL) :
    FarApart 2 {p}RestRegion B :=
  farApart_unionL h

/-- The moving box of the answer glider, at generation `t` after the cut. -/
def {p}AnsF (t : ℕ) : Set Cell :=
  {fa('t')}

/-- The footprint of the tail: the region of the rest and the moving box of the answer. -/
def {p}TailF (t : ℕ) : Set Cell :=
  {p}RestRegion ∪ {p}AnsF t

set_option maxRecDepth 100000 in
/-- **The answer is far from the rest**, at every generation of the tail. -/
theorem {p}AnsFar (t : ℕ) : FarApart 2 {p}RestRegion ({p}AnsF t) :=
  {p}RestRegion_far ⟨{(',' + chr(10) + '    ').join(
        ['BU.farApart_box (by omega)'] * len(comps) +
        (['regLanes_farApart_box (by omega)'] if diag else []))}, trivial⟩
''']
    # tail segments: FootInT
    for k in range(K0, last + 1):
        s = segs[k]
        Lcall = f'{p}L{k}' + (' ' + ' '.join(lnames(s['binders'])) if lnames(s['binders']) else '')
        proofs = []
        for j, pr in enumerate(s['procs']):
            proofs.append(ans_proof(pr) if j == ans[k] else rest_proof(pr, s['n'], True))
        out.append(f'''set_option maxRecDepth 100000 in
/-- Every process of segment {k} stays in the footprint of the tail. -/
theorem {p}FootS{k}{s['sbinders'].rstrip()} :
    FootInT (n := {s['n']}) {p}TailF {offs[k]} ({Lcall}) :=
  ⟨{(',' + chr(10) + '   ').join(proofs)},
   trivial⟩
''')
    # the rest list at the cut, and its footprint
    s = segs[K0]
    lb = s['binders']
    Lrest = [pr for j, pr in enumerate(s['procs']) if j != ans[K0]]
    out.append(f'''/-- The processes of segment {K0} other than the answer. -/
def {p}LrestS{lb.rstrip()} :
    List (Proc {s['n']}) :=
  [{(',' + chr(10) + '   ').join(Lrest)}]
''')
    LrestCall = f'{p}LrestS' + (' ' + ' '.join(lnames(lb)) if lnames(lb) else '')
    LK0call = f'{p}L{K0}' + (' ' + ' '.join(lnames(lb)) if lnames(lb) else '')
    out.append(f'''set_option maxRecDepth 100000 in
/-- The processes of segment {K0} other than the answer stay in the region of the rest. -/
theorem {p}FootRestS{s['sbinders'].rstrip()} :
    FootIn (n := {s['n']}) {p}RestRegion ({LrestCall}) :=
  ⟨{(',' + chr(10) + '   ').join(rest_proof(pr, s['n'], False) for pr in Lrest)},
   trivial⟩

set_option maxRecDepth 100000 in
/-- The start of segment {K0}: the rest and the answer. -/
theorem {p}StartS{s['sbinders'].rstrip()} :
    Proc.start ({LK0call}) = Proc.start ({LrestCall}) ∪ {A0} := by
  simp only [{p}L{K0}, {p}LrestS, Proc.start_cons, Proc.start_nil]
  ac_rfl
''')
    # the chains
    rm = re.search(r'theorem ' + p + r'Run\b(.*?):\s*\n?\s*conway\.evolve (\d+) \((Proc\.start [^)]*?|'
                   r'Proc\.start \([^)]*\))\) =\s*(Proc\.stop .*?) := by', run, re.S)
    runbinders, N = rm.group(1), int(rm.group(2))
    start, stop = rm.group(3), rm.group(4).strip()
    seqs = re.findall(r'(\(?' + p + r'Seg(\d+)( [^)]*)?\)?)\.evolve_eq', run)
    gls = re.findall(r'(' + p + r'Gl(\d+)(?: [^,\]\n]*)?)[,\]]', run[rm.end():])
    gls = [g_ for g_ in gls if 'Gl' in g_[0]]
    segargs = {int(k): (a or '') for (_, k, a) in seqs}
    glarg = {int(k): c for (c, k) in gls}
    Tcut = sum(segs[k]['n'] for k in range(K0))
    # prefix
    terms = [f'(Reaction.ofFootIn ({p}Seg{k}{segargs[k]}) ({p}FootG{k}{segargs[k]}))'
             for k in range(K0)]
    expr = terms[-1]
    for i in range(K0 - 2, -1, -1):
        expr = f'Reaction.seqC {terms[i]}\n    ({glarg[i].strip()})\n    ({expr})'
    out.append(f'''set_option maxRecDepth 100000 in
/-- **The run up to the cut**, inside the region of the run. -/
theorem {p}PreS{runbinders.rstrip()} :
    Reaction ({start}) (Proc.start ({LrestCall}) ∪ {A0}) {Tcut}
      (fun _ => {p}Region) :=
  (Reaction.castN
    ({expr})
    (by norm_num)).congrPQ rfl (({glarg[K0 - 1].strip()}).trans ({p}StartS{segargs[K0]}))
''')
    # tail joint
    terms = [f'(Reaction.ofFootInT (o := {offs[k]}) ({p}Seg{k}{segargs[k]}) ({p}FootS{k}{segargs[k]}))'
             for k in range(K0, last + 1)]
    expr = terms[-1]
    for i in range(len(terms) - 2, -1, -1):
        expr = f'Reaction.seqT {terms[i]}\n    ({glarg[K0 + i].strip()})\n    ({expr})'
    # answer chain, with the moving box of the answer as a time-dependent footprint
    def amono(k):
        pr = segs[k]['procs'][ans[k]]
        core = 'box_subset_of (by omega)'
        if '∩ UVBox' in fx_of(pr):
            core = f'Set.inter_subset_left.trans ({core})'
        return (f'(({rx(pr)}).mono (F\' := fun i => {p}AnsF (i + {offs[k]})) '
                f'fun i hi => {core})')
    aterms = [amono(k) for k in range(K0, last + 1)]
    aexpr = aterms[-1]
    for i in range(len(aterms) - 2, -1, -1):
        aexpr = f'Reaction.seqT (T := {p}AnsF) {aterms[i]} rfl\n    ({aexpr})'
    out.append(f'''set_option maxRecDepth 100000 in
/-- The tail of the run, from the cut, with the footprint of the tail. -/
theorem {p}TailS{runbinders.rstrip()} :
    Reaction (Proc.start ({LK0call})) ({stop}) {Ttail} (fun i => {p}TailF (i + 0)) :=
  Reaction.castN
    ({expr})
    (by norm_num)

set_option maxRecDepth 100000 in
/-- **The flight of the answer** after the cut, inside its moving box. -/
theorem {p}AnsS :
    Reaction {A0} {Alast} {Ttail} (fun t => {p}AnsF (t + 0)) :=
  Reaction.castN
    ({aexpr})
    (by norm_num)
''')
    out.append(f'''set_option maxRecDepth 100000 in
/-- **The rest of the run on its own**: after the cut, the circuit (and the register diagonal)
evolve inside `{p}RestRegion`, and the end of the run is their end with the answer's. -/
theorem {p}RestS{runbinders.rstrip()} :
    Reaction (Proc.start ({LrestCall})) (conway.evolve {Ttail} (Proc.start ({LrestCall})))
        {Ttail} (fun _ => {p}RestRegion) ∧
      {stop} = conway.evolve {Ttail} (Proc.start ({LrestCall})) ∪ {Alast} := by
  have h := {p}TailS{runbinders and ' ' + ' '.join(lnames(runbinders))}
  rw [{p}StartS{segargs[K0]}] at h
  exact Reaction.split (G := fun _ => {p}RestRegion) h {p}AnsS
    ((Proc.start_subset_foot _).trans
      (Proc.foot_subset_of_footIn _ ({p}FootRestS{segargs[K0]}) 0 (Nat.zero_le _)))
    (fun i _ => {p}AnsFar (i + 0))
    (fun i _ => ({p}AnsFar (i + 1 + 0)).mono_radius (by norm_num))
''')
    # the rest list of the last segment
    sl = segs[last]
    LrestE = [pr for j, pr in enumerate(sl['procs']) if j != ans[last]]
    if last != K0:
        out.append(f'''/-- The processes of the last segment other than the answer. -/
def {p}LrestE{sl['binders'].rstrip()} :
    List (Proc {sl['n']}) :=
  [{(',' + chr(10) + '   ').join(LrestE)}]

set_option maxRecDepth 100000 in
/-- The processes of the last segment other than the answer stay in the region of the rest. -/
theorem {p}FootRestE{sl['sbinders'].rstrip()} :
    FootIn (n := {sl['n']}) {p}RestRegion ({p}LrestE{' ' + ' '.join(lnames(sl['binders'])) if lnames(sl['binders']) else ''}) :=
  ⟨{(',' + chr(10) + '   ').join(rest_proof(pr, sl['n'], False) for pr in LrestE)},
   trivial⟩
''')
        LEname, FEname = f'{p}LrestE', f'{p}FootRestE'
    else:
        LEname, FEname = f'{p}LrestS', f'{p}FootRestS'
    LEcall = LEname + (' ' + ' '.join(lnames(sl['binders'])) if lnames(sl['binders']) else '')
    LLcall = f'{p}L{last}' + (' ' + ' '.join(lnames(sl['binders'])) if lnames(sl['binders']) else '')
    fm = re.search(r'(/--(?:(?!-/).)*?-/)\s*\ntheorem (' + p + r'(?:Run_rest|Op))\b(.*?):\s*\n\s*conway\.evolve '
                   + str(N) + r'\s*', run, re.S)
    name, fbinders = fm.group(2), fm.group(3)
    i0 = fm.end()
    j0 = E.match_close(run, i0)
    X = run[i0 + 1:j0]
    em = re.match(r'\s*=\s*(.*?) := by\n(.*?)\n\nend', run[j0 + 1:], re.S)
    Y = em.group(1).strip()
    prf = em.group(2)
    adef = re.search(r'def ' + Alast + r' : Finset Cell :=\s*(ofRows .*?\])', data, re.S).group(1)
    adef = ' '.join(adef.split())
    assert (' ∪ ' + adef) in Y, (adef, Y)
    Yrest = Y.replace(' ∪ ' + adef, '', 1)
    hl = re.search(r'have h := ' + p + r'Run(.*?)\n', prf).group(1)
    simpl = re.search(r'simp only \[(.*?)\] at h', prf, re.S).group(1)
    simpl = simpl.replace(f'{p}L{last},', f'{p}L{last}, {LEname},')
    rw = re.search(r'rw \[(' + p + r'Rest)\]', prf).group(1)
    out.append(f'''set_option maxRecDepth 100000 in
/-- **`{name}` with the answer split off**: up to generation {Tcut} the run stays in `{p}Region` and
reaches the rest and the answer glider `{A0}`; then the rest alone reaches the circuit's end
inside `{p}RestRegion` in {Ttail} generations (the answer flies on by `{p}AnsS`). -/
theorem {name}S{fbinders.rstrip()} :
    Reaction ({X}) (Proc.start ({LrestCall}) ∪ {A0}) {Tcut}
        (fun _ => {p}Region) ∧
      Reaction (Proc.start ({LrestCall})) ({Yrest}) {Ttail} (fun _ => {p}RestRegion) := by
  have hpre := {p}PreS{hl}
  have hrest := {p}RestS{hl}
  have hs : Proc.start ({p}L0{(' ' + ' '.join(lnames(segs[0]['binders']))) if lnames(segs[0]['binders']) else ''}) = {X} := by
    simp only [{simpl}]
    rw [{rw}]
    ac_rfl
  have eY : Proc.stop ({LEcall}) = {Yrest} := by
    simp only [{simpl}]
    rw [{rw}]
    ac_rfl
  have eL : Proc.stop ({LLcall}) = Proc.stop ({LEcall}) ∪ {Alast} := by
    simp only [{p}L{last}, {LEname}, Proc.stop_cons, Proc.stop_nil]
    ac_rfl
  have hY : (({Yrest} : Finset Cell) : Set Cell) ⊆ {p}RestRegion := by
    rw [← eY]
    exact (Proc.stop_subset_foot _).trans
      (Proc.foot_subset_of_footIn _ ({FEname}{segargs[last]}) _ le_rfl)
  have hA : (({Alast} : Finset Cell) : Set Cell) ⊆ {p}AnsF ({Ttail} + 0) := by
    rw [← {p}AnsS.evolve_eq]
    exact {p}AnsS.subset _ le_rfl
  have hfar := ({p}AnsFar ({Ttail} + 0)).sep hY hA
  have hfar' := ({p}AnsFar ({Ttail} + 0)).sep (hrest.1.subset _ le_rfl) hA
  have e := hrest.2.symm.trans (eL.trans (by rw [eY]))
  refine ⟨hpre.congrPQ hs rfl, ?_⟩
  rw [← union_cancel_right e hfar'.disjoint hfar.disjoint]
  exact hrest.1

end LeanTheory.Life
''')
    with open(os.path.join(GEN, P + 'Split.lean'), 'w') as f:
        f.write('\n'.join(out))
    print(P + 'Split.lean', 'cut', K0, 'tail', Ttail, 'components', len(regl))


if __name__ == '__main__':
    main()
