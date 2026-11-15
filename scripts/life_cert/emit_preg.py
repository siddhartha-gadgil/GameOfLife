#!/usr/bin/env python3
"""Emit `<Prefix>PreG.lean`: a generated run up to a cut segment, with a region made of components.

Research note N-22. Usage: emit_preg.py PREFIX K0. Same as `emit_rung.py`, restricted to the
segments before `K0` (the region of the run before its answer flies alone).

Original description of emit_rung:

Like `emit_runr.py`, but the region of the run is `unionL <p>RegL`, a short list of components
`BU a b lo hi U1 U2 V1 V2` (a box in x, y intersected with a box in u = x - y, v = x + y) and, for
the register runs, the lanes `regLanes`: a piece is far from the run when it is far from every
component (`<p>Region_far`).

Reads the generated files `Gen/<Prefix>Data.lean`, `Gen/<Prefix>Seg*.lean`, `Gen/<Prefix>Run.lean`
and writes `Gen/<Prefix>RunG.lean` with

* `<p>FootK`: every process of segment `K` stays in the region `U` (a box, together with the lanes
  of the register diagonal `regLanes` for the runs with the diagonal);
* `<p>RunG`: the run as a reaction with the constant footprint `<p>Region`;
* `<final>G`: the final statement of the run (`<p>Run_rest` or `<p>Op`) as a reaction.

Untrusted: Lean checks every statement.

Usage: emit_runr.py PREFIX   (e.g. dz2d, bodyInc)
"""
import glob
import os
import re
import sys

GEN = os.path.join(os.path.dirname(__file__), '..', '..', 'LeanTheory', 'Theory', 'Life', 'Gen')


def read(path):
    with open(path) as f:
        return f.read()


def split_top(s):
    """Split a list body at top-level commas."""
    out, depth, cur = [], 0, []
    for ch in s:
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(''.join(cur))
            cur = []
        else:
            cur.append(ch)
    if ''.join(cur).strip():
        out.append(''.join(cur))
    return [x.strip() for x in out]


def match_close(s, i):
    """Index of the bracket closing the one at `s[i]`."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] in '([{⟨':
            depth += 1
        elif s[j] in ')]}⟩':
            depth -= 1
            if depth == 0:
                return j
    raise ValueError('unbalanced')


NUM = r'\(?(-?\d+)\)?'
MOV = r'\(?\(?(-?\d+)\)? \+ \(\(i / 4 : ℕ\) : ℤ\) \* \(?(-?\d+)\)?\)'


def parse_box(expr, n):
    """Range of the `Box` part of a footprint over `i ≤ n`: (a, b, lo, hi, moving)."""
    m = re.match(r'fun _ => Box ' + ' '.join([NUM] * 4) + r'\s*$', expr)
    if m:
        a, b, lo, hi = map(int, m.groups())
        return (a, b, lo, hi, False)
    m = re.match(r'fun i => Box ' + ' '.join([MOV] * 4), expr)
    if m:
        g = list(map(int, m.groups()))
        q = n // 4
        rng = []
        for k in range(4):
            c, d = g[2 * k], g[2 * k + 1]
            rng.append((min(c, c + q * d), max(c, c + q * d)))
        return (rng[0][0], rng[1][1], rng[2][0], rng[3][1], True)
    return None

UVMOV = r'UVBox ' + ' '.join([MOV] * 4)


def swept(c, d, q):
    return (min(c, c + q * d), max(c, c + q * d))


def comp_of(fx, n):
    """The component of a footprint over `i <= n`: (a, b, lo, hi, U1, U2, V1, V2, kind)."""
    m = re.match(r'fun _ => Box ' + ' '.join([NUM] * 4) + r'\s*$', fx)
    if m:
        a, b, lo, hi = map(int, m.groups())
        return (a, b, lo, hi, a - hi, b - lo, a + lo, b + hi, 'box')
    m = re.match(r'fun i => Box ' + ' '.join([MOV] * 4), fx)
    if not m:
        return None
    q = n // 4
    g = list(map(int, m.groups()))
    (a0, da), (b0, db), (l0, dl), (h0, dh) = [(g[2 * k], g[2 * k + 1]) for k in range(4)]
    xa, xb = swept(a0, da, q)[0], swept(b0, db, q)[1]
    ylo, yhi = swept(l0, dl, q)[0], swept(h0, dh, q)[1]
    mu = re.search(UVMOV, fx)
    if mu:
        h = list(map(int, mu.groups()))
        U1 = swept(h[0], h[1], q)[0]
        U2 = swept(h[2], h[3], q)[1]
        V1 = swept(h[4], h[5], q)[0]
        V2 = swept(h[6], h[7], q)[1]
        return (xa, xb, ylo, yhi, U1, U2, V1, V2, 'movuv')
    us = [a0 + t * da - (h0 + t * dh) for t in (0, q)]
    us2 = [b0 + t * db - (l0 + t * dl) for t in (0, q)]
    vs = [a0 + t * da + (l0 + t * dl) for t in (0, q)]
    vs2 = [b0 + t * db + (h0 + t * dh) for t in (0, q)]
    return (xa, xb, ylo, yhi, min(us), max(us2), min(vs), max(vs2), 'mov')


def contains(C, c):
    return (C[0] <= c[0] and c[1] <= C[1] and C[2] <= c[2] and c[3] <= C[3] and C[4] <= c[4] and
            c[5] <= C[5] and C[6] <= c[6] and c[7] <= C[7])


def hull(c, d):
    return (min(c[0], d[0]), max(c[1], d[1]), min(c[2], d[2]), max(c[3], d[3]),
            min(c[4], d[4]), max(c[5], d[5]), min(c[6], d[6]), max(c[7], d[7]))


def mergeable(c, d):
    if (c[4], c[5]) == (d[4], d[5]) and c[6] <= d[7] + 2 and d[6] <= c[7] + 2:
        return True
    if (c[6], c[7]) == (d[6], d[7]) and c[4] <= d[5] + 2 and d[4] <= c[5] + 2:
        return True
    return contains(c, d) or contains(d, c)


def merge_all(cs):
    cs = list(dict.fromkeys(cs))
    changed = True
    while changed:
        changed = False
        for i in range(len(cs)):
            for j in range(i + 1, len(cs)):
                if mergeable(cs[i], cs[j]):
                    h = hull(cs[i], cs[j])
                    cs = [x for k, x in enumerate(cs) if k not in (i, j)] + [h]
                    changed = True
                    break
            if changed:
                break
    return cs


def bu(c):
    return 'BU ' + ' '.join(f'({x})' for x in c[:8])


def memproof(idx):
    s = 'List.mem_cons_self'
    for _ in range(idx):
        s = f'List.mem_cons_of_mem _ ({s})'
    return s


def main():
    p = sys.argv[1]
    P = p[0].upper() + p[1:]
    data = read(os.path.join(GEN, P + 'Data.lean'))
    pieces = {}
    for m in re.finditer(r'def (' + p + r'G\d+) : Piece :=\s*⟨\w+, ' + ', '.join([NUM] * 4), data):
        pieces[m.group(1)] = tuple(map(int, m.groups()[1:]))
    segs = {}
    for f in glob.glob(os.path.join(GEN, P + 'Seg*.lean')):
        txt = read(f)
        for m in re.finditer(r'def (' + p + r'L(\d+))(.*?):\s*List \(Proc (\d+)\) :=\s*\n', txt,
                             re.S):
            k = int(m.group(2))
            binders = m.group(3)
            n = int(m.group(4))
            st = txt.index('[', m.end())
            body = txt[st + 1:match_close(txt, st)]
            hm = re.search(r'theorem ' + p + 'Seg' + str(k) + r'\b(.*?):\s*\n?\s*Reaction', txt,
                           re.S)
            segs[k] = dict(binders=binders, n=n, procs=split_top(body),
                           sbinders=hm.group(1) if hm else '')
    K0 = int(sys.argv[2])
    segs = {k: v for k, v in segs.items() if k < K0}
    run = read(os.path.join(GEN, P + 'Run.lean'))
    alltxt = ''.join(''.join(s['procs']) for s in segs.values())
    diag = 'wStrip' in alltxt or 'PullG' in alltxt
    pullg = 'PullG' in alltxt
    # components
    comps = []
    early = None
    if pullg:
        early = (48, 147, 139, 238, -107, -75, 187, 385)
        comps.append(early)
    for s_ in segs.values():
        for pr in s_['procs']:
            if pr.startswith('Piece.bundle'):
                names = re.findall(p + r'G\d+', pr[:pr.index(']')])
                for x in names:
                    a, b, lo, hi = pieces[x]
                    comps.append((a, b, lo, hi, a - hi, b - lo, a + lo, b + hi))
            else:
                fx = re.search(r'F := (.*?),\s*reaction :=', pr, re.S).group(1)
                c = comp_of(fx, s_['n'])
                if c is not None:
                    comps.append(c[:8])
    comps = merge_all(comps)
    lanes_idx = len(comps) if diag else None
    nL = len(comps) + (1 if diag else 0)

    def find(c):
        for k, C in enumerate(comps):
            if contains(C, c):
                return k, C
        raise SystemExit('no component for ' + str(c))
    region = f'{p}PreRegion'
    out = []
    out.append(f'''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Gen.{P}Run
public import LeanTheory.Theory.Life.RunRegion

/-!
# Generated: the region of the run `{p}`

Generated by `scripts/life_cert/emit_rung.py` from the generated segments; the generator is
untrusted, Lean checks every step. The whole run stays in `{p}PreRegion`, a union of {nL}
components.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-- The components of the region of the run `{p}`. -/
def {p}PreRegL : List (Set Cell) :=
  [{(','+chr(10)+'   ').join([bu(c) for c in comps] + (['regLanes'] if diag else []))}]

/-- The region of the run `{p}`. -/
def {p}PreRegion : Set Cell := unionL {p}PreRegL

/-- A set far from every component is far from the region of the run. -/
theorem {p}PreRegion_far {{B : Set Cell}} (h : FarAll B {p}PreRegL) : FarApart 2 {p}PreRegion B :=
  farApart_unionL h
''')
    if pullg:
        ei = comps.index(find(early)[1])
        out.append(f'''/-- The salvo and the block of the generic process stay in the region of the run: the salvo in
a component while near the circuit, then in the lanes of the register diagonal. -/
theorem {p}PullG_subP (k j : ℕ) : {p}PullG k j ⊆ {region} := by
  intro c hc
  have h : c ∈ {bu(comps[ei])} ∨ c ∈ regLanes := by
    simp only [{p}PullG] at hc
    split_ifs at hc <;>
      simp only [BU, Box, UVBox, regLanes, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
        at hc ⊢ <;> omega
  rcases h with h | h
  · exact mem_unionL (L := {p}PreRegL) ({memproof(ei)}) h
  · exact mem_unionL (L := {p}PreRegL) ({memproof(lanes_idx)}) h
''')
    for k in sorted(segs):
        s = segs[k]
        n = s['n']
        Largs = ' '.join(re.findall(r'\((\w+)(?: \w+)* :', s['binders']))
        Lnames = []
        bt = s['binders']
        j = 0
        while j < len(bt):
            if bt[j] == '(':
                e = match_close(bt, j)
                Lnames += bt[j + 1:e].split(':')[0].split()
                j = e + 1
            else:
                j += 1
        Lcall = f'{p}L{k}' + (' ' + ' '.join(Lnames) if Lnames else '')
        proofs = []
        for pr in s['procs']:
            if pr.startswith('Piece.bundle'):
                names = re.findall(p + r'G\d+', pr[:pr.index(']')])
                bs = []
                for x in names:
                    a, b, lo, hi = pieces[x]
                    k_, C = find((a, b, lo, hi, a - hi, b - lo, a + lo, b + hi))
                    bs.append(f'subset_unionL (X := {bu(C)}) ({memproof(k_)}) '
                              f'(box_subset_BU (a := {a}) (b := {b}) (lo := {lo}) (hi := {hi}) '
                              f'(by norm_num))')
                proofs.append('fun i _ => Piece.bundle_F_subset (L := [' + ', '.join(names) +
                              ']) ⟨' + ', '.join(bs) + ', trivial⟩ i')
            else:
                fx = re.search(r'F := (.*?),\s*reaction :=', pr, re.S).group(1)
                c = comp_of(fx, n)
                if 'PullG' in fx:
                    am = re.search(r'PullG (\w+) \(i \+ (\d+)\)', fx)
                    proofs.append(f'fun i _ => {p}PullG_subP {am.group(1)} (i + {am.group(2)})')
                elif 'wStrip' in fx:
                    proofs.append(f'fun i hi => (wStrip_subset_regLanes (by omega) (by omega)).trans '
                                  f'(subset_unionL (L := {p}PreRegL) ({memproof(lanes_idx)}) '
                                  f'subset_rfl)')
                elif c is None:
                    proofs.append(f'fun i _ => subset_unionL (L := {p}PreRegL) '
                                  f'({memproof(lanes_idx)}) (fun c hc => by '
                                  f'simp only [Box, regLanes, Set.mem_ofPred_eq] at hc ⊢; omega)')
                else:
                    k_, C = find(c[:8])
                    lem = 'boxUV_subset_BU' if c[8] == 'movuv' else 'box_subset_BU'
                    tac = 'norm_num' if c[8] == 'box' else 'omega'
                    proofs.append(f'fun i hi => subset_unionL (X := {bu(C)}) ({memproof(k_)}) '
                                  f'({lem} (by {tac}))')
        out.append(f'''set_option maxRecDepth 100000 in
/-- Every process of segment {k} stays in the region of the run. -/
theorem {p}FootP{k}{s['sbinders'].rstrip()} :
    FootIn (n := {n}) {region} ({Lcall}) :=
  ⟨{(',' + chr(10) + '   ').join(proofs)},
   trivial⟩
''')
    # the chain, from the Run proof
    rm = re.search(r'theorem ' + p + r'Run\b(.*?):\s*\n?\s*conway\.evolve (\d+) \((Proc\.start [^)]*?|Proc\.start \([^)]*\))\) =\s*'
                   r'(Proc\.stop .*?) := by', run, re.S)
    runbinders, N = rm.group(1), int(rm.group(2))
    start, stop = rm.group(3), rm.group(4).strip()
    seqs = re.findall(r'(\(?' + p + r'Seg(\d+)( [^)]*)?\)?)\.evolve_eq', run)
    gls = re.findall(r'(' + p + r'Gl(\d+)(?: [^,\]\n]*)?)[,\]]', run[rm.end():])
    gls = [g for g in gls if 'Gl' in g[0]]
    segargs = {int(k): (a or '') for (_, k, a) in seqs}
    glarg = {int(k_): c for (c, k_) in gls}
    Tcut = sum(segs[k]['n'] for k in range(K0))
    terms = [f'(Reaction.ofFootIn ({p}Seg{k}{segargs[k]}) ({p}FootP{k}{segargs[k]}))'
             for k in range(K0)]
    expr = terms[-1]
    for i in range(K0 - 2, -1, -1):
        expr = f'Reaction.seqC {terms[i]}\n    ({glarg[i].strip()})\n    ({expr})'
    bt = segs[K0 - 1]['binders']
    names, jj = [], 0
    while jj < len(bt):
        if bt[jj] == '(':
            e = match_close(bt, jj)
            names += bt[jj + 1:e].split(':')[0].split()
            jj = e + 1
        else:
            jj += 1
    LARGS = (' ' + ' '.join(names)) if names else ''
    out.append(f'''set_option maxRecDepth 100000 in
/-- **The run up to segment {K0}** ({Tcut} generations) inside the region of that part of the run. -/
theorem {p}PreG{runbinders.rstrip()} :
    Reaction ({start}) (Proc.stop ({p}L{K0 - 1}{LARGS})) {Tcut} (fun _ => {region}) :=
  Reaction.castN
    ({expr})
    (by norm_num)

end LeanTheory.Life
''')
    with open(os.path.join(GEN, P + 'PreG.lean'), 'w') as f:
        f.write('\n'.join(out))
    print(P + 'PreG.lean', region, 'segments', len(segs))


if __name__ == '__main__':
    main()
