#!/usr/bin/env python3
"""Emit the generated part of `DecSepThr5.lean`: the rest regions of the register runs are far from
the hulls of the station footprints (untrusted generator; Lean checks every statement).

Usage: emit_dsep_st.py OUT.lean   (writes the generated lemmas; the file is completed by hand)"""
import sys

NZREST = ['dz2dRestRegL', 'dz2d1RestRegL', 'dz2d2RestRegL', 'dz2d3RestRegL'] + \
    ['dz2mk%dRestRegL' % k for k in range(1, 8)]


def one(L, box, doc):
    return '''
set_option maxRecDepth 100000 in
/-- `%(L)s` is far from %(doc)s. -/
theorem dsepT_%(L)s_st : ∀ k : ℤ, 0 ≤ k →
    FarApart 2 (unionL %(L)s)
      (%(box)s) := by
  intro k hk
  refine farApart_unionL ?_
  simp only [%(L)s, FarAll]
  dsepT_fa
''' % {'L': L, 'box': box, 'doc': doc}


def main(out):
    parts = []
    for L in NZREST:
        parts.append(one(L, 'Box (380 + 72 * k) (467 + 72 * k) (784 + 72 * k) (919 + 72 * k)',
                         'the hull of NZ station `k`'))
    parts.append(one('dz2mk0RestRegL',
                     'Box (849 + 72 * k) (979 + 72 * k) (-385 - 72 * k) (-293 - 72 * k)',
                     'the hull of Z station `k`'))
    open(out, 'w').write(''.join(parts))


if __name__ == '__main__':
    main(sys.argv[1])
