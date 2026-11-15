/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Life.Gen.Dz2jRunR

/-!
# The increment of a static block, with its footprint

`dz2jAll` (the increment of the register block at any position `k`, research notes `N-20`,
`N-22`) as a reaction inside the box of the circuit together with the lanes of the register
diagonal. Used for small register values, when every salvo of the queue has arrived.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

set_option linter.style.longLine false

set_option maxRecDepth 100000 in
/-- Every process of the tail of the run stays in the region of the run. -/
theorem dz2jTailFoot (k : ℕ) :
    FootIn (n := 4 * k) (Box (-1395) (668) (-1489) (659) ∪ regLanes) (dz2jLT k) :=
  ⟨fun i _ => dz2jPullG_sub k (i + 685),
   fun i _ => Piece.bundle_F_subset (L := [dz2jG0, dz2jG1, dz2jG2, dz2jG3, dz2jG4, dz2jG5, dz2jG6, dz2jG7, dz2jG8, dz2jG9, dz2jG10, dz2jG11, dz2jG12, dz2jG13, dz2jG14, dz2jG15, dz2jG16, dz2jG17, dz2jG18, dz2jG19, dz2jG20, dz2jG21, dz2jG22, dz2jG23, dz2jG24, dz2jG25, dz2jG26, dz2jG27])
     ⟨box_subset_union_left (a := -94) (b := 128) (lo := -79) (hi := 132) (by norm_num),
      box_subset_union_left (a := -5) (b := 113) (lo := -136) (hi := -104) (by norm_num),
      box_subset_union_left (a := -121) (b := -31) (lo := -394) (hi := -362) (by norm_num),
      box_subset_union_left (a := -86) (b := 49) (lo := -332) (hi := -296) (by norm_num),
      box_subset_union_left (a := -3) (b := 19) (lo := -260) (hi := -252) (by norm_num),
      box_subset_union_left (a := -47) (b := -39) (lo := -244) (hi := -222) (by norm_num),
      box_subset_union_left (a := -347) (b := -339) (lo := -101) (hi := -79) (by norm_num),
      box_subset_union_left (a := -101) (b := -11) (lo := 189) (hi := 221) (by norm_num),
      box_subset_union_left (a := -560) (b := -528) (lo := -587) (hi := -497) (by norm_num),
      box_subset_union_left (a := -498) (b := -466) (lo := -552) (hi := -462) (by norm_num),
      box_subset_union_left (a := -274) (b := -252) (lo := -806) (hi := -798) (by norm_num),
      box_subset_union_left (a := 463) (b := 471) (lo := -69) (hi := -47) (by norm_num),
      box_subset_union_left (a := -29) (b := 3) (lo := 350) (hi := 440) (by norm_num),
      box_subset_union_left (a := 28) (b := 50) (lo := 376) (hi := 384) (by norm_num),
      box_subset_union_left (a := -1100) (b := -1010) (lo := -1100) (hi := -1068) (by norm_num),
      box_subset_union_left (a := -945) (b := -855) (lo := -918) (hi := -886) (by norm_num),
      box_subset_union_left (a := -1395) (b := -1387) (lo := -738) (hi := -716) (by norm_num),
      box_subset_union_left (a := -79) (b := 11) (lo := 627) (hi := 659) (by norm_num),
      box_subset_union_left (a := 543) (b := 633) (lo := -23) (hi := 9) (by norm_num),
      box_subset_union_left (a := 578) (b := 668) (lo := -85) (hi := -53) (by norm_num),
      box_subset_union_left (a := -808) (b := -718) (lo := -1402) (hi := -1370) (by norm_num),
      box_subset_union_left (a := -843) (b := -753) (lo := -1464) (hi := -1432) (by norm_num),
      box_subset_union_left (a := -835) (b := -813) (lo := -1489) (hi := -1481) (by norm_num),
      box_subset_union_left (a := -1329) (b := -1321) (lo := -981) (hi := -959) (by norm_num),
      box_subset_union_left (a := -700) (b := -678) (lo := -1476) (hi := -1468) (by norm_num),
      box_subset_union_left (a := -651) (b := -643) (lo := -1427) (hi := -1405) (by norm_num),
      box_subset_union_left (a := -873) (b := -865) (lo := -1210) (hi := -1188) (by norm_num),
      box_subset_union_left (a := -843) (b := -753) (lo := -1143) (hi := -1111) (by norm_num), trivial⟩ i,
   trivial⟩

set_option maxRecDepth 100000 in
/-- **`dz2jAll` with its footprint**: the increment of the block at any `k` stays in the box of the
circuit and the lanes of the register diagonal. -/
theorem dz2jAllR (k : ℕ) (hk : 0 ≤ k) :
    Reaction (dz2jRest ∪ ofRows (-857) (-1054) [6, 5, 4] ∪ reg1Block ↑k)
      (conway.evolve (4 * k) dz2jRest ∪ reg1Block (↑k + 1)) (4 * k + 6990)
      (fun _ => (Box (-1395) (668) (-1489) (659) ∪ regLanes)) := by
  have hs : Proc.start (dz2jL0 k) = dz2jRest ∪ ofRows (-857) (-1054) [6, 5, 4] ∪ reg1Block ↑k := by
    simp only [dz2jL0, dz2jRest, dz2jA0, dz2jG0, dz2jG1, dz2jG2, dz2jG3, dz2jG4, dz2jG5, dz2jG6, dz2jG7, dz2jG8, dz2jG9, dz2jG10, dz2jG11, dz2jG12, dz2jG13, dz2jG14, dz2jG15, dz2jG16, dz2jG17, dz2jG18, dz2jG19, dz2jG20, dz2jG21, dz2jG22, dz2jG23, dz2jG24, dz2jG25, dz2jG26, dz2jG27, Proc.start_cons, Proc.start_nil, Piece.bundle, Piece.idle,
      List.map_cons, List.map_nil, union_empty, Rule.evolve_zero]
    ac_rfl
  have hb := (Piece.bundle dz2jPieces dz2jPieces_sep 0 (4 * k) ((4 * k + 0) % 30) rfl).reaction.evolve_eq
  simp only [dz2jPieces, dz2jG0, dz2jG1, dz2jG2, dz2jG3, dz2jG4, dz2jG5, dz2jG6, dz2jG7, dz2jG8, dz2jG9, dz2jG10, dz2jG11, dz2jG12, dz2jG13, dz2jG14, dz2jG15, dz2jG16, dz2jG17, dz2jG18, dz2jG19, dz2jG20, dz2jG21, dz2jG22, dz2jG23, dz2jG24, dz2jG25, dz2jG26, dz2jG27, Proc.start_cons, Proc.start_nil, Proc.stop_cons, Proc.stop_nil,
    Piece.bundle, Piece.idle, List.map_cons, List.map_nil, union_empty, Rule.evolve_zero] at hb
  have h := Reaction.seqC (dz2jRunR k hk) (dz2jGlT k)
    (Reaction.ofFootIn (dz2jTail k hk) (dz2jTailFoot k))
  refine (h.castN (by ring)).congrPQ hs ?_
  rw [dz2jRest, hb, ← dz2jPullEnd k]
  simp only [dz2jLT, dz2jPieces, dz2jG0, dz2jG1, dz2jG2, dz2jG3, dz2jG4, dz2jG5, dz2jG6, dz2jG7, dz2jG8, dz2jG9, dz2jG10, dz2jG11, dz2jG12, dz2jG13, dz2jG14, dz2jG15, dz2jG16, dz2jG17, dz2jG18, dz2jG19, dz2jG20, dz2jG21, dz2jG22, dz2jG23, dz2jG24, dz2jG25, dz2jG26, dz2jG27, Proc.stop_cons, Proc.stop_nil, Piece.bundle, Piece.idle,
    List.map_cons, List.map_nil, union_empty]
  ac_rfl

end LeanTheory.Life
