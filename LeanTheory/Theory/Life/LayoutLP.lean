/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Computability.CounterMachine
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The provable program layout `LP`: closed formulas and separation inequalities

Report `R-31` (the project's own search, script `scripts/life_lp/p1_layout.py`) lays out the
Life machine of a counter-machine program by closed formulas: every position is affine in the
indices (instruction `i`, register `r`, caller `j` with `q = D - 1 - j`, entry copy `t`,
sub-band `b`, slot `s`) and in the global parameters `N, R, D, P` of the program, with parity
corrections `fixp` and residue corrections given by `mod` formulas. This module defines these
formulas as computable functions of a `Program` (rotated coordinates `u = x - y`, `v = x + y`)
and proves, for **every** program and every valid index, the separation inequalities of `R-31`
§3 and the arithmetic timing facts of §4.1–4.2. The geometry of the parts (unit templates, the
register module `M(D)`) enters only through named constants taken from `R-31` §1–2 and
`p0_parts.py`; their correctness is the business of the local certificates, not of this module.

Main results:

* parameters: `one_le_R`, `one_le_D`, `one_le_P`, and the pitches `≡ 0 (mod 30)` (`PU_mod`,
  `PM_mod`, `VT_mod`, `U0_mod`, `HI_mod`, `A_mod`, `U_mod`);
* the 17 pair classes of `R-31` §3: `sep01_unitSlabs` … `sep17_diagonal_band` (#13 is the
  combination `sep13_*` of the column, track and hairpin facts with the region facts);
* parities of the corners: `track_corner_odd`, `inCol_side_odd`, `copyBeta_spec`,
  `decChan_parity`, `incChan_parity`, `nzTokChan_parity`, `nzAnsChan_parity`, `zTokChan_parity`,
  `zAnsChan_parity`;
* the nesting lemma `nested_no_crossing` and its instance `decJz_nested` for the decJz trio
  `KNZ ⊃ C ⊃ KZ`;
* timing: `lenDown_eq`, `lenUp_eq` (Manhattan length of a route), `timeUp_mod`, `timeDown_mod`
  (the residue of a route time does not depend on `i, a, r, b, N, R, P`), `window_rule`,
  `eC_eq_window`, `C_residue`, `sigma_spec`, `eN_spec`, `eKZ_spec`, `delta_NZ`, `delta_Z`.
-/

@[expose] public section

namespace LeanTheory.Life

open LeanTheory.Computability

namespace LP

/-! ### Global parameters of a program -/

/-- One more than the register of an instruction (`0` for `halt`). -/
def regBound : Instr → ℕ
  | .inc r => r + 1
  | .decJz r _ => r + 1
  | .halt => 0

/-- The number of registers `R = 1 + max r` (at least `1`). -/
def numRegs (p : Program) : ℕ := max 1 ((p.map regBound).foldr max 0)

/-- Whether an instruction is a `decJz` on register `r`. -/
def isDecOn (r : ℕ) : Instr → Bool
  | .decJz r' _ => r' == r
  | _ => false

/-- The number of `decJz` callers of register `r`. -/
def decCount (p : Program) (r : ℕ) : ℕ := (p.filter (isDecOn r)).length

/-- `D = max(1, max_r #decJz on r)`: the number of callers of the uniform module `M(D)`. -/
def numCallers (p : Program) : ℕ :=
  max 1 (((List.range (numRegs p)).map (decCount p)).foldr max 0)

/-- The predecessors that instruction `ins` (number `i`) gives to unit `a` (`N` instructions):
an `inc r` feeds unit `i + 1` (continue) and the merge unit `N + r` (INC link); a `decJz r z`
feeds unit `i + 1` (NZ answer) and unit `z` (Z answer). -/
def predContrib (N a i : ℕ) : Instr → ℕ
  | .inc r => (if i + 1 = a then 1 else 0) + (if N + r = a then 1 else 0)
  | .decJz _ z => (if i + 1 = a then 1 else 0) + (if z = a then 1 else 0)
  | .halt => 0

/-- The number of predecessors of unit `a` (the start counts for unit `0`). -/
def predCount (p : Program) (a : ℕ) : ℕ :=
  (if a = 0 then 1 else 0) +
    ((List.range p.length).map fun i => (p[i]?.map (predContrib p.length a i)).getD 0).sum

/-- `P = max(1, max #predecessors)` over the units `a < N + R`. -/
def numPreds (p : Program) : ℕ :=
  max 1 (((List.range (p.length + numRegs p)).map (predCount p)).foldr max 0)

/-- The number `N` of instructions. -/
def N (p : Program) : ℤ := p.length

/-- The number `R` of registers. -/
def R (p : Program) : ℤ := numRegs p

/-- The number `D` of callers per module. -/
def D (p : Program) : ℤ := numCallers p

/-- The maximal number `P` of predecessors of a unit (entry chains have `2P` copies). -/
def P (p : Program) : ℤ := numPreds p

/-- The number `NB = 2 + N + R` of sub-bands reserved in the band. -/
def NB (p : Program) : ℤ := 2 + N p + R p

theorem zero_le_N (p : Program) : 0 ≤ N p := by simp [N]

/-- At least one register. -/
theorem one_le_R (p : Program) : 1 ≤ R p := by
  simp only [R, numRegs]; exact_mod_cast le_max_left _ _

/-- At least one caller. -/
theorem one_le_D (p : Program) : 1 ≤ D p := by
  simp only [D, numCallers]; exact_mod_cast le_max_left _ _

/-- At least one predecessor. -/
theorem one_le_P (p : Program) : 1 ≤ P p := by
  simp only [P, numPreds]; exact_mod_cast le_max_left _ _

/-! ### Rounding and parity -/

/-- `⌈x / 30⌉` (Euclidean division by a positive literal is the floor). -/
def ceil30 (x : ℤ) : ℤ := (x + 29) / 30

/-- `⌈x / 120⌉`. -/
def ceil120 (x : ℤ) : ℤ := (x + 119) / 120

/-- `fixp c π`: `c` or `c - 1`, the one of parity `π` (`p1_layout.fixp`). -/
def fixp (c π : ℤ) : ℤ := c - (c - π) % 2

/-- `fixp c π` is `c` or `c - 1`. -/
theorem fixp_bounds (c π : ℤ) : c - 1 ≤ fixp c π ∧ fixp c π ≤ c := by
  unfold fixp; omega

/-- `fixp c π` has the parity of `π`. -/
theorem fixp_parity (c π : ℤ) : (fixp c π - π) % 2 = 0 := by
  unfold fixp; omega

/-! ### Unit templates (`R-31` §1.2, `p0_parts.py`) -/

/-- Unit pitch `P_U = 540 + 180 P`. -/
def PU (p : Program) : ℤ := 540 + 180 * P p

/-- Left edge of the unit slab, `-206 - 122 P` (the `dec` template, last entry copy `- 30`;
`p0_parts.UnitLP.left`, asserted in `p1_layout.layout`). -/
def slabL (p : Program) : ℤ := -206 - 122 * P p

/-- Right edge of the unit slab, `max(238, 86 + 58 P)` (`dec`: box `208 + 30`; `halt`/`merge`:
box `56 + 58 P`, `+ 30`; `p0_parts.UnitLP.right`, asserted in `p1_layout.layout`). -/
def slabR (p : Program) : ℤ := max 238 (86 + 58 * P p)

/-- Unit row bottom: the unit templates reach `v ≤ 1523` (local; `R-31` §1.2). -/
def unitBottom : ℤ := 1523

/-- First input column of a `dec` unit, `C0 = -237`. -/
def C0dec : ℤ := -237

/-- First input column of an `inc` unit, `C0 = -91`. -/
def C0inc : ℤ := -91

/-- First input column of a `halt` / `merge` unit, `C0 = -67`. -/
def C0halt : ℤ := -67

/-- Input column of entry copy `t`: `c_in(t) = C0 - 61 t`. -/
def inCol (C0 t : ℤ) : ℤ := C0 - 61 * t

/-- Side line of entry copy `t`: `v_t = 76 - 99 t`. -/
def sideV (t : ℤ) : ℤ := 76 - 99 * t

/-- Source column `L` of the `dec` unit (KNZ), `-155`. -/
def decL : ℤ := -155

/-- Source column `R` of the `dec` unit (C), `127`. -/
def decR : ℤ := 127

/-- Source column `D'` of the `dec` unit (KZ, after the jog), `188`. -/
def decD : ℤ := 188

/-- Source column `D` of the `inc` unit (continue), `68`. -/
def incD : ℤ := 68

/-- Source column `R` of the `inc` unit (INC link), `157`. -/
def incR : ℤ := 157

/-- Source column `D` of the `halt` and `merge` units, `14`. -/
def haltD : ℤ := 14

/-- The entry copy used by predecessor number `e`: `t = 2 e + β`, `β = (C0 - c) mod 2`, so that
the input column has the parity of the source column `c`. -/
def copyIdx (C0 e c : ℤ) : ℤ := 2 * e + (C0 - c) % 2

/-! ### Positions of units, band and modules (`R-31` §2) -/

/-- Unit `a` at `u = A_a = P_U a`. -/
def A (p : Program) (a : ℤ) : ℤ := PU p * a

/-- Band top `V_T = -30 ⌈(3444 + 198 D + 660 NB) / 30⌉`. -/
def VT (p : Program) : ℤ := -30 * ceil30 (3444 + 198 * D p + 660 * NB p)

/-- Unit row `V_U = V_T - 1644`. -/
def VU (p : Program) : ℤ := VT p - 1644

/-- Module pitch `P_M = 2400 + 540 D`. -/
def PM (p : Program) : ℤ := 2400 + 540 * D p

/-- `U_0 = 30 ⌈(P_U (N + R - 1) + max(238, 86 + 58P) + 943 + 248 D) / 30⌉`. -/
def U0 (p : Program) : ℤ := 30 * ceil30 (PU p * (N p + R p - 1) + slabR p + 943 + 248 * D p)

/-- Module `r` at `u`-shift `U_r = U_0 + P_M r` (and `v`-shift `0`). -/
def U (p : Program) (r : ℤ) : ℤ := U0 p + PM p * r

/-- Hairpin base `H_I = 30 ⌊(-716 - 122 P) / 30⌋`. -/
def HI (p : Program) : ℤ := 30 * ((-716 - 122 * P p) / 30)

/-- Top of the module `M(D)` (module frame): `v = -3324 - 198 D` (`R-31` §1.3, `uvbox`). -/
def modTop (p : Program) : ℤ := -3324 - 198 * D p

/-- Left end of the module with its zones (module frame): `u = -823 - 248 D`. -/
def modLeft (p : Program) : ℤ := -823 - 248 * D p

/-- Right end of the module with its zones (module frame): `u = 1378 + 268 D`. -/
def modRight (p : Program) : ℤ := 1378 + 268 * D p

/-- The register diagonal of module `r`: `u = U_r - 96` (for `v ≥ 404`). -/
def diagU (p : Program) (r : ℤ) : ℤ := U p r - 96

/-- The diagonal starts at `v = 404`. -/
def diagV0 : ℤ := 404

/-! ### Zones of the module (module frame, `R-31` §1.3) -/

/-- Left zone edge `u_L = -793`. -/
def uL : ℤ := -793

/-- Right zone edge `u_R = 1410 + 144 D`. -/
def uR (p : Program) : ℤ := 1410 + 144 * D p

/-- Port line of DEC copy `t`: `v = -3351 - 99 (2D - 1 - t)`. -/
def decPortV (p : Program) (t : ℤ) : ℤ := -3351 - 99 * (2 * D p - 1 - t)

/-- Port line of the INC copy, `v = -2347`. -/
def incPortV : ℤ := -2347

/-- Port line of the NZ token of caller `j`, `v = 1256 + 144 j`. -/
def nzTokPortV (j : ℤ) : ℤ := 1256 + 144 * j

/-- Port line of the NZ answer of caller `j`, `v = 1325 + 144 j`. -/
def nzAnsPortV (j : ℤ) : ℤ := 1325 + 144 * j

/-- Left-zone channel number `idx` for a port line `v`: `fixp (u_L - 62 idx) (1 - v mod 2)`. -/
def leftChan (idx v : ℤ) : ℤ := fixp (uL - 62 * idx) (1 - v % 2)

/-- Channel of DEC copy `t` (index `t`). -/
def decChan (p : Program) (t : ℤ) : ℤ := leftChan t (decPortV p t)

/-- Channel of the INC copy (index `2D`). -/
def incChan (p : Program) : ℤ := leftChan (2 * D p) incPortV

/-- Channel of the NZ token of caller `j` (index `2D + 1 + 2j`). -/
def nzTokChan (p : Program) (j : ℤ) : ℤ := leftChan (2 * D p + 1 + 2 * j) (nzTokPortV j)

/-- Channel of the NZ answer of caller `j` (index `2D + 2 + 2j`). -/
def nzAnsChan (p : Program) (j : ℤ) : ℤ := leftChan (2 * D p + 2 + 2 * j) (nzAnsPortV j)

/-- Station column of the Z answer of caller `j` (SE line), `1301 + 144 j`. -/
def zAnsStation (j : ℤ) : ℤ := 1301 + 144 * j

/-- Station column of the Z token of caller `j` (NW line), `1230 + 144 j`. -/
def zTokStation (j : ℤ) : ℤ := 1230 + 144 * j

/-- The Z stations end at `v ≤ 681` (module frame, `R-31` §1.3). -/
def zStationBottom : ℤ := 681

/-- The reversed caller index `q = D - 1 - j`. -/
def qOf (p : Program) (j : ℤ) : ℤ := D p - 1 - j

/-- Turn depth of the Z answer: `v_d = fixp (1500 + 180 q) (1 - station mod 2)`. -/
def zAnsDepth (p : Program) (j : ℤ) : ℤ := fixp (1500 + 180 * qOf p j) (1 - zAnsStation j % 2)

/-- Turn depth of the Z token: `w_d = v_d + 61`. -/
def zTokDepth (p : Program) (j : ℤ) : ℤ := zAnsDepth p j + 61

/-- Channel of the Z answer: `fixp (u_R + 124 q) (1 - v_d mod 2)`. -/
def zAnsChan (p : Program) (j : ℤ) : ℤ := fixp (uR p + 124 * qOf p j) (1 - zAnsDepth p j % 2)

/-- Channel of the Z token: `fixp (u_R + 124 q + 62) (1 - w_d mod 2)`. -/
def zTokChan (p : Program) (j : ℤ) : ℤ :=
  fixp (uR p + 124 * qOf p j + 62) (1 - zTokDepth p j % 2)

/-! ### Sub-bands, tracks, hairpins -/

/-- Sub-band of instruction `i` (sub-band `0` is the halt sub-band). -/
def instrBand (i : ℤ) : ℤ := 1 + i

/-- Sub-band of the merge unit of register `r`. -/
def mergeBand (p : Program) (r : ℤ) : ℤ := 1 + N p + r

/-- Track number `k ∈ [0, 9]` of sub-band `b` with parity correction `π`. -/
def track (p : Program) (b k π : ℤ) : ℤ := VT p + 660 * b + 62 * k + π

/-- `OUT` track of slot `s` for a source column `c`: `V_T + 660 b + 62 s + π`,
`π = 1 - c mod 2`. -/
def trackOut (p : Program) (b s c : ℤ) : ℤ := track p b s (1 - c % 2)

/-- `BACK` track of slot `s` for a source column `c`: `V_T + 660 b + 62 (9 - s) + π`. -/
def trackBack (p : Program) (b s c : ℤ) : ℤ := track p b (9 - s) (1 - c % 2)

/-- Regular hairpin of slot `s` with residue correction `e` for a source column `c`:
`fixp (H_I + 90 s - 2 e) (c mod 2)`. -/
def hairReg (p : Program) (s e c : ℤ) : ℤ := fixp (HI p + 90 * s - 2 * e) (c % 2)

/-- Hairpin of an INC continue with extra delay `G`: `fixp (H_I - 62 - G - 2 e) (c mod 2)`. -/
def hairCont (p : Program) (G e c : ℤ) : ℤ := fixp (HI p - 62 - G - 2 * e) (c % 2)

/-! ### decJz tokens (`R-31` §4.2) -/

/-- `e_C = 9 q mod 15`: the window rule for the fitted residue `r0_C = 4 + 18 q`. -/
def eC (q : ℤ) : ℤ := 9 * q % 15

/-- `σ = 2 (q mod 2)`: extra slots of `C`. -/
def sigma (q : ℤ) : ℤ := 2 * (q % 2)

/-- `dN0 = -3936 - 228 q`: KNZ token minus target for `E_N = 0` (fitted, `R-31` §4.2). -/
def dN0 (q : ℤ) : ℤ := -3936 - 228 * q

/-- `dZ0 = 367 + 1564 q - 8 e_C`: KZ token minus target for `e_KZ = 0` (fitted). -/
def dZ0 (q : ℤ) : ℤ := 367 + 1564 * q - 8 * eC q

/-- `x = max(0, ⌈(368 + 1564 q - 8 e_C - 30 σ) / 120⌉)`: whole periods by which `C` is moved. -/
def xC (q : ℤ) : ℤ := max 0 (ceil120 (368 + 1564 * q - 8 * eC q - 30 * sigma q))

/-- The total hairpin steps of `C`: `e_C + 4 σ + 15 x`. -/
def eCtot (q : ℤ) : ℤ := eC q + 4 * sigma q + 15 * xC q

/-- `E_N = (3936 + 228 q - 2 σ) / 8`: extra steps of the KNZ hairpin. -/
def eN (q : ℤ) : ℤ := (3936 + 228 * q - 2 * sigma q) / 8

/-- `e_KZ = (-1 - dZ0 + 30 σ + 120 x) / 8`. -/
def eKZ (q : ℤ) : ℤ := (-1 - dZ0 q + 30 * sigma q + 120 * xC q) / 8

/-- The hairpin of `C` for caller `q`: `fixp (H_I + 90 - 2 (e_C + 4σ + 15x)) (c mod 2)`. -/
def hairC (p : Program) (q c : ℤ) : ℤ := fixp (HI p + 90 - 2 * eCtot q) (c % 2)

/-- The hairpin of KNZ: `fixp (H_C - 62 - 2 E_N) (c mod 2)` (`cC`: the source column of `C`). -/
def hairKNZ (p : Program) (q cC c : ℤ) : ℤ := fixp (hairC p q cC - 62 - 2 * eN q) (c % 2)

/-- The hairpin of KZ (slot `2`, `e = e_KZ`). -/
def hairKZ (p : Program) (q c : ℤ) : ℤ := hairReg p 2 (eKZ q) c

/-! ### Basic arithmetic of the parameters -/

/-- `A_{a+1} = A_a + P_U`. -/
theorem A_succ (p : Program) (a : ℤ) : A p (a + 1) = A p a + PU p := by
  unfold A; ring

/-- Monotonicity: `a < a' → A_a + P_U ≤ A_{a'}`. -/
theorem A_add_le (p : Program) {a a' : ℤ} (h : a < a') : A p a + PU p ≤ A p a' := by
  have hP := one_le_P p
  have : A p a' - A p a = PU p * (a' - a) := by unfold A; ring
  have h1 : (0 : ℤ) ≤ PU p := by unfold PU; omega
  nlinarith

/-- `U_{r+1} = U_r + P_M`. -/
theorem U_succ (p : Program) (r : ℤ) : U p (r + 1) = U p r + PM p := by
  unfold U; ring

theorem PU_mod (p : Program) : PU p % 30 = 0 := by unfold PU; omega

theorem PM_mod (p : Program) : PM p % 30 = 0 := by unfold PM; omega

theorem VT_mod (p : Program) : VT p % 30 = 0 := by unfold VT; omega

theorem U0_mod (p : Program) : U0 p % 30 = 0 := by unfold U0; omega

theorem HI_mod (p : Program) : HI p % 30 = 0 := by unfold HI; omega

/-- Every unit position is `≡ 0 (mod 30)`. -/
theorem A_mod (p : Program) (a : ℤ) : A p a % 30 = 0 := by
  unfold A; rw [Int.mul_emod, PU_mod]; simp

/-- Every module shift is `≡ 0 (mod 30)` (in particular even: the block translation
`(148 + U_r / 2, 240 - U_r / 2)` is exact). -/
theorem U_mod (p : Program) (r : ℤ) : U p r % 30 = 0 := by
  unfold U; rw [Int.add_emod, Int.mul_emod, PM_mod, U0_mod]; simp

/-! ### The separation inequalities of `R-31` §3 -/

/-- **#1** Unit slab `a` / slab `a + 1`, margin `274 + 58 P - max(238, 86 + 58 P)`
(`= 36 + 58 P` for `P ≤ 2`, `188` for `P ≥ 3`). -/
theorem sep01_unitSlabs (p : Program) (a : ℤ) :
    A p (a + 1) + slabL p - (A p a + slabR p + 60) = 274 + 58 * P p - max 238 (86 + 58 * P p)
      ∧ A p a + slabR p + 60 + 36 + 58 ≤ A p (a + 1) + slabL p := by
  have := one_le_P p
  rw [A_succ]; unfold PU slabL slabR; omega

/-- **#1'** Any two unit slabs `a < a'` are `≥ 60` apart (the monotonicity form). -/
theorem sep01_unitSlabs_lt (p : Program) {a a' : ℤ} (h : a < a') :
    A p a + slabR p + 60 ≤ A p a' + slabL p := by
  have := A_add_le p h
  have := one_le_P p
  unfold PU slabL slabR at *; omega

/-- **#2** Unit row / band: `V_U + 1523 ≤ V_T - 120`, margin exactly `1`. -/
theorem sep02_unitRow_band (p : Program) : VU p + unitBottom + 1 = VT p - 120 := by
  unfold VU unitBottom; omega

/-- **#3** Band / modules: `V_T + 660 NB ≤ -3324 - 198 D - 120`, margin in `[0, 29]`. -/
theorem sep03_band_modules (p : Program) :
    VT p + 660 * NB p ≤ modTop p - 120 ∧ modTop p - 120 - (VT p + 660 * NB p) ≤ 29 := by
  unfold VT modTop ceil30; omega

/-- **#4** Sub-bands: every track of sub-band `b` is in `V_T + 660 b + [0, 559]`, and a track of
sub-band `b` is `≥ 101` above every track of a later sub-band. -/
theorem sep04_subbands (p : Program) {b b' k k' π π' : ℤ} (hb : b < b') (hk : 0 ≤ k ∧ k ≤ 9)
    (hk' : 0 ≤ k' ∧ k' ≤ 9) (hπ : 0 ≤ π ∧ π ≤ 1) (hπ' : 0 ≤ π' ∧ π' ≤ 1) :
    VT p + 660 * b ≤ track p b k π ∧ track p b k π ≤ VT p + 660 * b + 559 ∧
      track p b k π + 101 ≤ track p b' k' π' := by
  unfold track; omega

/-- **#5** Tracks of one sub-band: distinct track numbers are `≥ 61` apart. -/
theorem sep05_tracks (p : Program) {b k k' π π' : ℤ} (hk : k < k') (hπ : 0 ≤ π ∧ π ≤ 1)
    (hπ' : 0 ≤ π' ∧ π' ≤ 1) : track p b k π + 61 ≤ track p b k' π' := by
  unfold track; omega

/-- **#5'** The `OUT` and `BACK` tracks of slots `s < s'` in `[0, 4]` are pairwise `≥ 61` apart
and in the mirror order `OUT_s < OUT_{s'} < BACK_{s'} < BACK_s` (whatever the source columns). -/
theorem sep05_slots (p : Program) {b s s' c c' : ℤ} (hs : 0 ≤ s) (hss : s < s') (hs' : s' ≤ 4) :
    trackOut p b s c + 61 ≤ trackOut p b s' c' ∧ trackOut p b s' c' + 61 ≤ trackBack p b s' c' ∧
      trackBack p b s' c' + 61 ≤ trackBack p b s c := by
  unfold trackOut trackBack track; omega

/-- **#6** Units / module `0` with its zones: every unit `a ≤ N + R - 1` ends `120` left of the
left zone of module `0`; for the last unit the margin is in `[0, 29]`. -/
theorem sep06_units_module0 (p : Program) {a : ℤ} (ha : a ≤ N p + R p - 1) :
    A p a + slabR p + 120 ≤ U0 p + modLeft p ∧
      U0 p + modLeft p - (A p (N p + R p - 1) + slabR p + 120) ≤ 29 := by
  have hm : A p a ≤ A p (N p + R p - 1) := by
    rcases ha.lt_or_eq with h | h
    · have := A_add_le p h
      have := one_le_P p
      unfold PU at *; omega
    · rw [h]
  unfold U0 modLeft ceil30 A at *; omega

/-- **#7** Module `r` / module `r + 1` (with zones), margin exactly `139 + 24 D`. -/
theorem sep07_modules (p : Program) (r : ℤ) :
    U p (r + 1) + modLeft p - (U p r + modRight p + 60) = 139 + 24 * D p := by
  rw [U_succ]; unfold PM modLeft modRight; omega

/-- **#8** Regular hairpins (slots `≤ 4`, `H ≤ H_I + 360`) / unit `0`: margin in `[30, 59]`. -/
theorem sep08_hairpins_unit0 (p : Program) :
    HI p + 360 + 30 ≤ A p 0 + slabL p - 120 ∧ A p 0 + slabL p - 120 - (HI p + 360) ≤ 59 := by
  unfold HI A slabL; simp only [mul_zero]; omega

/-- Every regular hairpin (slot `s ≤ 4`, `e ≥ 0`) is at `u ≤ H_I + 360`. -/
theorem hairReg_le (p : Program) {s e c : ℤ} (hs : s ≤ 4) (he : 0 ≤ e) :
    hairReg p s e c ≤ HI p + 360 := by
  have := fixp_bounds (HI p + 90 * s - 2 * e) (c % 2)
  unfold hairReg; omega

/-- **#9a** Regular hairpins of slots `s < s'` (`e, e' ∈ [0, 14]`) are `≥ 61` apart. The margin
`61` is attained (`s' = s + 1`, `e' = 14`, `e = 0`, parity correction `1`): `R-31` claims
`≥ 62`. -/
theorem sep09_hairReg (p : Program) {s s' e e' c c' : ℤ} (hs : s < s') (he : 0 ≤ e ∧ e ≤ 14)
    (he' : 0 ≤ e' ∧ e' ≤ 14) : hairReg p s e c + 61 ≤ hairReg p s' e' c' := by
  have := fixp_bounds (HI p + 90 * s - 2 * e) (c % 2)
  have := fixp_bounds (HI p + 90 * s' - 2 * e') (c' % 2)
  unfold hairReg at *; omega

/-- **#9b** In an `inc` sub-band the continue's hairpin (`G ≥ 0`) is `≥ 123` left of the INC
link's (slot `1`). -/
theorem sep09_inc (p : Program) {G e e' c c' : ℤ} (hG : 0 ≤ G) (he : 0 ≤ e)
    (he' : 0 ≤ e' ∧ e' ≤ 14) : hairCont p G e c + 123 ≤ hairReg p 1 e' c' := by
  have := fixp_bounds (HI p - 62 - G - 2 * e) (c % 2)
  have := fixp_bounds (HI p + 90 * 1 - 2 * e') (c' % 2)
  unfold hairCont hairReg at *; omega

/-! ### Arithmetic of the decJz token formulas (`R-31` §4.2) -/

theorem eC_bounds (q : ℤ) : 0 ≤ eC q ∧ eC q ≤ 14 := by unfold eC; omega

theorem sigma_bounds (q : ℤ) : 0 ≤ sigma q ∧ sigma q ≤ 2 := by unfold sigma; omega

/-- For `q ≥ 0` the quantity under the ceiling of `x` is positive, so `x` is the ceiling itself
and `120 x - (368 + 1564 q - 8 e_C - 30 σ) ∈ [0, 119]`. -/
theorem xC_spec {q : ℤ} (hq : 0 ≤ q) :
    0 ≤ 120 * xC q - (368 + 1564 * q - 8 * eC q - 30 * sigma q) ∧
      120 * xC q - (368 + 1564 * q - 8 * eC q - 30 * sigma q) ≤ 119 ∧ 1 ≤ xC q := by
  unfold xC ceil120 eC sigma; omega

/-- `E_N` is exact: `8 E_N = 3936 + 228 q - 2 σ`; and `E_N ≥ 492`. -/
theorem eN_spec {q : ℤ} (hq : 0 ≤ q) : 8 * eN q = 3936 + 228 * q - 2 * sigma q ∧ 492 ≤ eN q := by
  unfold eN sigma; omega

/-- `e_KZ` is exact and in `[0, 14]`: `8 e_KZ = -1 - dZ0 + 30 σ + 120 x`. -/
theorem eKZ_spec {q : ℤ} (hq : 0 ≤ q) :
    8 * eKZ q = -1 - dZ0 q + 30 * sigma q + 120 * xC q ∧ 0 ≤ eKZ q ∧ eKZ q ≤ 14 := by
  have := xC_spec hq
  unfold eKZ dZ0 at *; unfold eC sigma at *; omega

/-- `σ = 2 (q mod 2)` is the **only** number of extra slots `σ' ∈ {0, 1, 2}` making
`dN0 - 30 σ' ≡ 0` and `dZ0 - 30 σ' ≡ 7 (mod 8)` (obstruction `O14`). -/
theorem sigma_spec (q σ' : ℤ) (h : 0 ≤ σ' ∧ σ' ≤ 2) :
    ((dN0 q - 30 * σ') % 8 = 0 ∧ (dZ0 q - 30 * σ') % 8 = 7) ↔ σ' = sigma q := by
  unfold dN0 dZ0 eC sigma; omega

/-- **The NZ token is exact** (`δ_NZ = 0`): `C` is moved by `4σ + 15x` hairpin steps
(`8 (4σ + 15x)` generations, so `C'` moves by the whole slots `30 σ + 120 x`); the KNZ hairpin
follows `C`'s and adds `E_N` steps. -/
theorem delta_NZ (q : ℤ) (hq : 0 ≤ q) :
    dN0 q + 8 * (4 * sigma q + 15 * xC q + eN q) - (30 * sigma q + 120 * xC q) = 0 := by
  have := eN_spec hq
  unfold dN0 at *; omega

/-- **The Z token is one generation early** (`δ_Z = -1`): the KZ hairpin does not follow `C`. -/
theorem delta_Z (q : ℤ) (hq : 0 ≤ q) :
    dZ0 q + 8 * eKZ q - (30 * sigma q + 120 * xC q) = -1 := by
  have := eKZ_spec hq
  omega

/-- **#9c** In a `decJz` sub-band (source columns `c_N, c_C, c_Z`, any parities): the hairpins
are ordered `KNZ < C < KZ < NZ answer (slot 3) < Z answer (slot 4)`, each `≥ 61` apart
(KNZ is even `≥ 62 + 2 E_N ≥ 1046` left of `C`). -/
theorem sep09_decJz (p : Program) {q cN cC cZ cA cB eA eB : ℤ} (hq : 0 ≤ q)
    (hA : 0 ≤ eA ∧ eA ≤ 14) (hB : 0 ≤ eB ∧ eB ≤ 14) :
    hairKNZ p q cC cN + 62 + 2 * eN q ≤ hairC p q cC ∧ hairC p q cC + 61 ≤ hairKZ p q cZ ∧
      hairKZ p q cZ + 61 ≤ hairReg p 3 eA cA ∧ hairReg p 3 eA cA + 61 ≤ hairReg p 4 eB cB := by
  have hK := eKZ_spec hq
  have h1 := fixp_bounds (hairC p q cC - 62 - 2 * eN q) (cN % 2)
  have h2 := fixp_bounds (HI p + 90 - 2 * eCtot q) (cC % 2)
  have h3 := fixp_bounds (HI p + 90 * 2 - 2 * eKZ q) (cZ % 2)
  have h4 := fixp_bounds (HI p + 90 * 3 - 2 * eA) (cA % 2)
  have h5 := fixp_bounds (HI p + 90 * 4 - 2 * eB) (cB % 2)
  have hx := xC_spec hq
  have := eC_bounds q
  have := sigma_bounds q
  unfold hairKNZ hairKZ hairReg at *
  unfold hairC at h1 ⊢
  unfold eCtot at *
  omega

/-- **#10** Columns of a unit slab: the input columns `C0 - 61 t` are pairwise `≥ 61` apart,
lie `≥ 82` (`dec`), `≥ 159` (`inc`), `≥ 81` (`halt`, `merge`) left of the source columns, the
source columns are `≥ 61` apart, and all lie `≥ 30` inside the slab for `t < 2P`. -/
theorem sep10_unitColumns (p : Program) {t t' : ℤ} (ht : 0 ≤ t) (htt : t < t')
    (ht' : t' < 2 * P p) :
    inCol C0dec t' + 61 ≤ inCol C0dec t ∧ inCol C0inc t' + 61 ≤ inCol C0inc t ∧
      inCol C0halt t' + 61 ≤ inCol C0halt t ∧
      inCol C0dec t + 82 ≤ decL ∧ decL + 61 ≤ decR ∧ decR + 61 ≤ decD ∧
      inCol C0inc t + 159 ≤ incD ∧ incD + 61 ≤ incR ∧ inCol C0halt t + 81 ≤ haltD ∧
      slabL p + 30 ≤ inCol C0dec t' ∧ slabL p + 30 ≤ inCol C0inc t' ∧
      slabL p + 30 ≤ inCol C0halt t' ∧ decD + 30 ≤ slabR p ∧ incR + 30 ≤ slabR p := by
  unfold inCol C0dec C0inc C0halt decL decR decD incD incR haltD slabL slabR; omega

/-- **#11a** Left-zone channels: distinct channel numbers are `≥ 61` apart (pitch `62`, parity
`-1`). -/
theorem sep11_leftChan {idx idx' v v' : ℤ} (h : idx < idx') :
    leftChan idx' v' + 61 ≤ leftChan idx v := by
  have := fixp_bounds (uL - 62 * idx) (1 - v % 2)
  have := fixp_bounds (uL - 62 * idx') (1 - v' % 2)
  unfold leftChan uL at *; omega

/-- The left-zone channel numbers `t` (DEC copy `t < 2D`), `2D` (INC), `2D + 1 + 2j` (NZ token),
`2D + 2 + 2j` (NZ answer) are distinct, and they all lie in `[0, 4D]` for `j < D`. -/
theorem leftChan_indices_distinct (p : Program) {t j j' : ℤ} (ht : 0 ≤ t ∧ t < 2 * D p)
    (hj : 0 ≤ j ∧ j < D p) (hj' : 0 ≤ j' ∧ j' < D p) :
    t ≠ 2 * D p ∧ t ≠ 2 * D p + 1 + 2 * j ∧ t ≠ 2 * D p + 2 + 2 * j ∧
      2 * D p ≠ 2 * D p + 1 + 2 * j ∧ 2 * D p ≠ 2 * D p + 2 + 2 * j ∧
      2 * D p + 1 + 2 * j ≠ 2 * D p + 2 + 2 * j' ∧
      (j ≠ j' → 2 * D p + 1 + 2 * j ≠ 2 * D p + 1 + 2 * j') ∧
      2 * D p + 2 + 2 * j ≤ 4 * D p ∧ 2 * D p + 2 + 2 * j' ≤ 4 * D p := by
  omega

/-- Every left-zone channel number in `[0, 4D]` lies in the module's extent
`[-823 - 248 D, -793]`. -/
theorem leftChan_in_extent (p : Program) {idx v : ℤ} (h : 0 ≤ idx ∧ idx ≤ 4 * D p) :
    modLeft p ≤ leftChan idx v ∧ leftChan idx v ≤ uL := by
  have := fixp_bounds (uL - 62 * idx) (1 - v % 2)
  unfold leftChan modLeft uL at *; omega

/-- **#11b** Right-zone channels: for callers `j ≠ j'` the four channels are pairwise `≥ 61`
apart, the Z token channel of `j` is `≥ 61` right of its Z answer channel, and all lie in
`[u_R - 1, 1378 + 268 D]`. -/
theorem sep11_rightChan (p : Program) {j j' : ℤ} (hj : 0 ≤ j ∧ j < D p) (hj' : 0 ≤ j' ∧ j' < D p)
    (hne : j' < j) :
    zAnsChan p j + 61 ≤ zTokChan p j ∧ zTokChan p j + 61 ≤ zAnsChan p j' ∧
      uR p - 1 ≤ zAnsChan p j ∧ zTokChan p j' ≤ modRight p := by
  have := fixp_bounds (uR p + 124 * qOf p j) (1 - zAnsDepth p j % 2)
  have := fixp_bounds (uR p + 124 * qOf p j + 62) (1 - zTokDepth p j % 2)
  have := fixp_bounds (uR p + 124 * qOf p j') (1 - zAnsDepth p j' % 2)
  have := fixp_bounds (uR p + 124 * qOf p j' + 62) (1 - zTokDepth p j' % 2)
  unfold zAnsChan zTokChan modRight uR qOf at *; omega

/-- The Z answer depth is exactly `v_d = 1500 + 180 q` (the station column `1301 + 144 j` is odd,
so the parity correction of `R-31`'s `(+π)` is `0`). -/
theorem zAnsDepth_eq (p : Program) (j : ℤ) : zAnsDepth p j = 1500 + 180 * qOf p j := by
  unfold zAnsDepth fixp zAnsStation; omega

/-- **#12** Right-zone depths: `w_d = v_d + 61`; for `j' < j` (so `q < q'`) the depths of `j'`
are `≥ 118` below those of `j`; all are `≥ 819` below the Z stations (`v ≤ 681`). -/
theorem sep12_depths (p : Program) {j j' : ℤ} (hj : j < D p) (hjj : j' < j) :
    zAnsDepth p j + 61 = zTokDepth p j ∧ zTokDepth p j + 118 ≤ zAnsDepth p j' ∧
      zStationBottom + 819 ≤ zAnsDepth p j := by
  have h1 := zAnsDepth_eq p j
  have h2 := zAnsDepth_eq p j'
  unfold zTokDepth zStationBottom qOf at *; omega

/-- **#13 (columns across regions)** A hairpin column (`≤ H_I + 360`) is `≥ 150` left of every
column of every unit slab `a ≥ 0`, and every column of a unit slab is `≥ 150` left of every column
of every module's left zone. With #4, #5, #9, #10, #11 (columns and tracks of one region pairwise
`≥ 61` apart) this gives the corner / foreign-segment separation. -/
theorem sep13_regions (p : Program) {a r h c c' : ℤ} (ha : 0 ≤ a ∧ a ≤ N p + R p - 1)
    (hr : 0 ≤ r) (hh : h ≤ HI p + 360) (hc : A p a + slabL p + 30 ≤ c ∧ c ≤ A p a + slabR p - 30)
    (hc' : U p r + modLeft p ≤ c') : h + 150 ≤ c ∧ c + 150 ≤ c' := by
  have h8 := sep08_hairpins_unit0 p
  have h6 := sep06_units_module0 p ha.2
  have hA : A p 0 ≤ A p a := by
    rcases ha.1.lt_or_eq with h | h
    · have := A_add_le p h
      have := one_le_P p
      unfold PU at *; omega
    · rw [← h]
  have hU : U0 p ≤ U p r := by
    have := one_le_D p
    unfold U PM; nlinarith
  omega

/-- **#14** Diagonal of `r` / left zone of `r`: `U_r - 96 - 60 - (U_r - 793) = 637`. -/
theorem sep14_diagonal_leftZone (p : Program) (r : ℤ) :
    diagU p r - 60 - (U p r + uL) = 637 := by
  unfold diagU uL; omega

/-- **#15** Diagonal / right zone and Z-station columns (`u ≥ U_r + 1230`), margin `1266`. -/
theorem sep15_diagonal_rightZone (p : Program) (r : ℤ) {j : ℤ} (hj : 0 ≤ j) :
    diagU p r + 60 + 1266 ≤ U p r + zTokStation j ∧ U p r + zTokStation j ≤ U p r + zAnsStation j
      ∧ U p r + zTokStation 0 ≤ U p r + uR p - 1 := by
  have := one_le_D p
  unfold diagU zTokStation zAnsStation uR; omega

/-- **#16** Diagonal of `r + 1` / right end of module `r`, margin exactly `866 + 272 D`. -/
theorem sep16_diagonal_nextModule (p : Program) (r : ℤ) :
    diagU p (r + 1) - 60 - (U p r + modRight p) = 866 + 272 * D p := by
  unfold diagU; rw [U_succ]; unfold PM modRight; omega

/-- **#17** Diagonal / band, units, hairpins: everything of the band and the units is at
`v < V_T + 660 NB ≤ -3444 - 198 D`, more than `3700` above the diagonal (`v ≥ 404`). -/
theorem sep17_diagonal_band (p : Program) :
    VU p + unitBottom < VT p ∧ VT p + 660 * NB p + 3700 < diagV0 := by
  have := sep03_band_modules p
  have := one_le_D p
  unfold VU unitBottom diagV0 modTop at *; omega

/-- **#17'** The diagonal of module `r ≥ 0` is right of every unit slab (by #6, #14). -/
theorem sep17_diagonal_units (p : Program) {a r : ℤ} (ha : a ≤ N p + R p - 1) (hr : 0 ≤ r) :
    A p a + slabR p + 120 + 60 ≤ diagU p r := by
  have h6 := (sep06_units_module0 p ha).1
  have hU : U0 p ≤ U p r := by
    have := one_le_D p
    unfold U PM; nlinarith
  have := one_le_D p
  unfold diagU modLeft at *; omega

/-! ### Parities of the corners -/

/-- A track corner is on an odd `u + v`: the source column `c` and the `OUT` (and `BACK`) track
with `π = 1 - c mod 2`; also the destination column `c'` if `c' ≡ c (mod 2)`. -/
theorem track_corner_odd (p : Program) (b s c c' : ℤ) (h : (c' - c) % 2 = 0) :
    (c + trackOut p b s c) % 2 = 1 ∧ (c' + trackBack p b s c) % 2 = 1 := by
  have := VT_mod p
  unfold trackOut trackBack track; omega

/-- A hairpin corner is on an odd `u + v` (the hairpin has the parity of the source column). -/
theorem hairReg_corner_odd (p : Program) (b s s' e c : ℤ) :
    (hairReg p s e c + trackOut p b s' c) % 2 = 1 ∧ (hairReg p s e c + trackBack p b s' c) % 2 = 1
    := by
  have := VT_mod p
  have := fixp_parity (HI p + 90 * s - 2 * e) (c % 2)
  unfold hairReg trackOut trackBack track at *; omega

/-- The input corners of every entry copy are on an odd `u + v` (`C0 + 76` is odd). -/
theorem inCol_side_odd (t : ℤ) :
    (inCol C0dec t + sideV t) % 2 = 1 ∧ (inCol C0inc t + sideV t) % 2 = 1 ∧
      (inCol C0halt t + sideV t) % 2 = 1 := by
  unfold inCol sideV C0dec C0inc C0halt; omega

/-- The entry copy `t = 2e + β` of predecessor number `e` is one of the copies `2e, 2e + 1` and
its input column has the parity of the source column `c`. -/
theorem copyBeta_spec (C0 e c : ℤ) :
    2 * e ≤ copyIdx C0 e c ∧ copyIdx C0 e c ≤ 2 * e + 1 ∧
      (inCol C0 (copyIdx C0 e c) - c) % 2 = 0 := by
  unfold copyIdx inCol; omega

/-- DEC copy `t = 2j` has an odd channel, as the `C` source column `A_i + 127`; its port corner
is on an odd `u + v`. -/
theorem decChan_parity (p : Program) (i r j : ℤ) :
    (U p r + decChan p (2 * j) - (A p i + decR)) % 2 = 0 ∧
      (decChan p (2 * j) + decPortV p (2 * j)) % 2 = 1 := by
  have := U_mod p r
  have := A_mod p i
  unfold decChan leftChan decPortV fixp uL decR; omega

/-- The INC channel is even, as the merge source column `A_{N+r} + 14`. -/
theorem incChan_parity (p : Program) (a r : ℤ) :
    (U p r + incChan p - (A p a + haltD)) % 2 = 0 ∧ (incChan p + incPortV) % 2 = 1 := by
  have := U_mod p r
  have := A_mod p a
  unfold incChan leftChan incPortV fixp uL haltD; omega

/-- The NZ token channel is odd, as the KNZ source column `A_i - 155`. -/
theorem nzTokChan_parity (p : Program) (i r j : ℤ) :
    (U p r + nzTokChan p j - (A p i + decL)) % 2 = 0 ∧ (nzTokChan p j + nzTokPortV j) % 2 = 1 := by
  have := U_mod p r
  have := A_mod p i
  unfold nzTokChan leftChan nzTokPortV fixp uL decL; omega

/-- The NZ answer channel corner (port line `1325 + 144 j`) is on an odd `u + v`. -/
theorem nzAnsChan_parity (p : Program) (j : ℤ) : (nzAnsChan p j + nzAnsPortV j) % 2 = 1 := by
  unfold nzAnsChan leftChan nzAnsPortV fixp uL; omega

/-- The Z token channel is even, as the KZ source column `A_i + 188`; its corners `(channel, w_d)`
and `(1230 + 144 j, w_d)` are on an odd `u + v` (the NW leg needs the even column: `R-31` §3). -/
theorem zTokChan_parity (p : Program) (i r j : ℤ) :
    (U p r + zTokChan p j - (A p i + decD)) % 2 = 0 ∧ (zTokChan p j + zTokDepth p j) % 2 = 1 ∧
      (zTokStation j + zTokDepth p j) % 2 = 1 := by
  have := U_mod p r
  have := A_mod p i
  have := zAnsDepth_eq p j
  unfold zTokChan zTokDepth fixp uR decD zTokStation qOf at *; omega

/-- The Z answer corners `(1301 + 144 j, v_d)` and `(channel, v_d)` are on an odd `u + v`. -/
theorem zAnsChan_parity (p : Program) (j : ℤ) :
    (zAnsStation j + zAnsDepth p j) % 2 = 1 ∧ (zAnsChan p j + zAnsDepth p j) % 2 = 1 := by
  have := zAnsDepth_eq p j
  unfold zAnsChan fixp uR zAnsStation qOf at *; omega

/-! ### The nesting lemma (`R-31` §3) -/

/-- A down-going U-route in one sub-band: source column `src` (vertical from `vs` down to `out`),
`OUT` track, hairpin column `hair`, `BACK` track, destination column `dst` (vertical from `back`
down to `vp`). -/
structure ULink where
  /-- Source column. -/
  src : ℤ
  /-- Start of the source vertical. -/
  vs : ℤ
  /-- `OUT` track. -/
  out : ℤ
  /-- Hairpin column. -/
  hair : ℤ
  /-- `BACK` track. -/
  back : ℤ
  /-- Destination column. -/
  dst : ℤ
  /-- End of the destination vertical. -/
  vp : ℤ

/-- A vertical segment (column `c`, `v ∈ [lo, hi]`) meets a horizontal one (track `w`,
`u ∈ [ulo, uhi]`). -/
def Meets (c lo hi w ulo uhi : ℤ) : Prop := lo ≤ w ∧ w ≤ hi ∧ ulo ≤ c ∧ c ≤ uhi

/-- No vertical segment of `l` meets a horizontal segment of `l'`. -/
def NoCross (l l' : ULink) : Prop :=
  ∀ c lo hi, (c, lo, hi) ∈ [(l.src, l.vs, l.out), (l.hair, l.out, l.back), (l.dst, l.back, l.vp)]
    → ∀ w ulo uhi, (w, ulo, uhi) ∈ [(l'.out, l'.hair, l'.src), (l'.back, l'.hair, l'.dst)] →
      ¬ Meets c lo hi w ulo uhi

/-- **Nesting lemma.** Outer link `o` and inner link `n` with `OUT_o < OUT_n < BACK_n < BACK_o`,
`H_o < H_n`, `s_o < s_n`, `d_o < d_n` do not cross: each vertical segment of one meets the
`v`-range of a horizontal segment of the other only outside its `u`-interval. -/
theorem nested_no_crossing (o n : ULink) (h1 : o.out < n.out) (h2 : n.out < n.back)
    (h3 : n.back < o.back) (h4 : o.hair < n.hair) (h5 : o.src < n.src) (h6 : o.dst < n.dst) :
    NoCross o n ∧ NoCross n o := by
  constructor <;>
  · intro c lo hi hv w ulo uhi hh
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hv hh
    unfold Meets
    omega

/-- The KNZ link of `decJz` number `i` on register `r`, caller `j` (`q = D - 1 - j`). -/
def linkKNZ (p : Program) (i r j vs : ℤ) : ULink where
  src := A p i + decL
  vs := vs
  out := trackOut p (instrBand i) 0 (A p i + decL)
  hair := hairKNZ p (qOf p j) (A p i + decR) (A p i + decL)
  back := trackBack p (instrBand i) 0 (A p i + decL)
  dst := U p r + nzTokChan p j
  vp := nzTokPortV j

/-- The C link of `decJz` number `i` on register `r`, caller `j` (to DEC copy `2j`). -/
def linkC (p : Program) (i r j vs : ℤ) : ULink where
  src := A p i + decR
  vs := vs
  out := trackOut p (instrBand i) 1 (A p i + decR)
  hair := hairC p (qOf p j) (A p i + decR)
  back := trackBack p (instrBand i) 1 (A p i + decR)
  dst := U p r + decChan p (2 * j)
  vp := decPortV p (2 * j)

/-- The KZ link of `decJz` number `i` on register `r`, caller `j` (down to the depth `w_d`). -/
def linkKZ (p : Program) (i r j vs : ℤ) : ULink where
  src := A p i + decD
  vs := vs
  out := trackOut p (instrBand i) 2 (A p i + decD)
  hair := hairKZ p (qOf p j) (A p i + decD)
  back := trackBack p (instrBand i) 2 (A p i + decD)
  dst := U p r + zTokChan p j
  vp := zTokDepth p j

/-- **The decJz trio is nested** (`KNZ ⊃ C ⊃ KZ`), for every program, every caller `j < D` and
every source `v`: none of the three concurrent links crosses another. Also the destination
verticals go down from the band (`BACK < v_port`) for `0 ≤ i < N`. -/
theorem decJz_nested (p : Program) {i r j vN vC vZ : ℤ} (hi : 0 ≤ i ∧ i < N p)
    (hj : 0 ≤ j ∧ j < D p) :
    NoCross (linkKNZ p i r j vN) (linkC p i r j vC) ∧ NoCross (linkC p i r j vC) (linkKNZ p i r j vN)
      ∧ NoCross (linkC p i r j vC) (linkKZ p i r j vZ)
      ∧ NoCross (linkKZ p i r j vZ) (linkC p i r j vC)
      ∧ (linkKNZ p i r j vN).back < (linkKNZ p i r j vN).vp
      ∧ (linkC p i r j vC).back < (linkC p i r j vC).vp
      ∧ (linkKZ p i r j vZ).back < (linkKZ p i r j vZ).vp := by
  have hD := one_le_D p
  have hq : 0 ≤ qOf p j := by unfold qOf; omega
  have h9 := sep09_decJz p (cN := A p i + decL) (cC := A p i + decR) (cZ := A p i + decD)
    (cA := 0) (cB := 0) (eA := 0) (eB := 0) hq (by omega) (by omega)
  have hN := eN_spec hq
  have hT := sep05_slots p (b := instrBand i) (s := 0) (s' := 1) (c := A p i + decL)
    (c' := A p i + decR) le_rfl (by omega) (by omega)
  have hT2 := sep05_slots p (b := instrBand i) (s := 1) (s' := 2) (c := A p i + decR)
    (c' := A p i + decD) (by omega) (by omega) (by omega)
  have hs : decL < decR ∧ decR < decD := by unfold decL decR decD; omega
  have hd1 : nzTokChan p j + 61 ≤ decChan p (2 * j) := sep11_leftChan (by omega)
  have hd2 : decChan p (2 * j) < zTokChan p j := by
    have h1 := leftChan_in_extent p (idx := 2 * j) (v := decPortV p (2 * j)) (by omega)
    have h2 := fixp_bounds (uR p + 124 * qOf p j + 62) (1 - zTokDepth p j % 2)
    unfold decChan zTokChan
    unfold uL uR qOf at *; omega
  have h3 := sep03_band_modules p
  have hRr := one_le_R p
  have hb : ∀ s c, trackBack p (instrBand i) s c ≤ VT p + 660 * N p + 62 * 9 - 62 * s + 661 := by
    intro s c; unfold trackBack track instrBand; omega
  have hd := zAnsDepth_eq p j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (nested_no_crossing _ _ (by simp only [linkKNZ, linkC]; omega) (by simp only [linkKNZ, linkC]; omega)
      (by simp only [linkKNZ, linkC]; omega) (by simp only [linkKNZ, linkC]; omega)
      (by simp only [linkKNZ, linkC]; omega) (by simp only [linkKNZ, linkC]; omega)).1
  · exact (nested_no_crossing _ _ (by simp only [linkKNZ, linkC]; omega) (by simp only [linkKNZ, linkC]; omega)
      (by simp only [linkKNZ, linkC]; omega) (by simp only [linkKNZ, linkC]; omega)
      (by simp only [linkKNZ, linkC]; omega) (by simp only [linkKNZ, linkC]; omega)).2
  · exact (nested_no_crossing _ _ (by simp only [linkKZ, linkC]; omega) (by simp only [linkKZ, linkC]; omega)
      (by simp only [linkKZ, linkC]; omega) (by simp only [linkKZ, linkC]; omega)
      (by simp only [linkKZ, linkC]; omega) (by simp only [linkKZ, linkC]; omega)).1
  · exact (nested_no_crossing _ _ (by simp only [linkKZ, linkC]; omega) (by simp only [linkKZ, linkC]; omega)
      (by simp only [linkKZ, linkC]; omega) (by simp only [linkKZ, linkC]; omega)
      (by simp only [linkKZ, linkC]; omega) (by simp only [linkKZ, linkC]; omega)).2
  · have := hb 0 (A p i + decL)
    simp only [linkKNZ]; unfold nzTokPortV NB modTop at *; omega
  · have := hb 1 (A p i + decR)
    simp only [linkC]; unfold decPortV NB modTop at *; omega
  · have := hb 2 (A p i + decD)
    simp only [linkKZ]; unfold zTokDepth NB modTop qOf at *; omega

/-! ### Timing (`R-31` §4.1) -/

/-- Manhattan length of a down-going route (source at `(us, vs)`, `OUT`, hairpin `H`, `BACK`,
channel `c`, port line `vp`, gate `ug`). -/
def lenDown (us vs out H back c vp ug : ℤ) : ℤ :=
  |out - vs| + |us - H| + |back - out| + |c - H| + |vp - back| + |ug - c|

/-- Manhattan length of an up-going route (to the side line `vt` of an entry copy). -/
def lenUp (us vs out H back c vt ug : ℤ) : ℤ :=
  |out - vs| + |us - H| + |back - out| + |c - H| + |back - vt| + |ug - c|

/-- The length of a down-going route is `v_port - v_src + s + u_gate - 2H`. -/
theorem lenDown_eq {us vs out H back c vp ug : ℤ} (h1 : vs ≤ out) (h2 : H ≤ us)
    (h3 : out ≤ back) (h4 : H ≤ c) (h5 : back ≤ vp) (h6 : c ≤ ug) :
    lenDown us vs out H back c vp ug = vp - vs + us + ug - 2 * H := by
  unfold lenDown
  rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ out - vs), abs_of_nonneg (by omega : (0 : ℤ) ≤ us - H),
    abs_of_nonneg (by omega : (0 : ℤ) ≤ back - out), abs_of_nonneg (by omega : (0 : ℤ) ≤ c - H),
    abs_of_nonneg (by omega : (0 : ℤ) ≤ vp - back), abs_of_nonneg (by omega : (0 : ℤ) ≤ ug - c)]
  ring

/-- The length of an up-going route is `2 BACK - v_src - v_t + s + u_gate - 2H`. -/
theorem lenUp_eq {us vs out H back c vt ug : ℤ} (h1 : vs ≤ out) (h2 : H ≤ us)
    (h3 : out ≤ back) (h4 : H ≤ c) (h5 : vt ≤ back) (h6 : c ≤ ug) :
    lenUp us vs out H back c vt ug = 2 * back - vs - vt + us + ug - 2 * H := by
  unfold lenUp
  rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ out - vs), abs_of_nonneg (by omega : (0 : ℤ) ≤ us - H),
    abs_of_nonneg (by omega : (0 : ℤ) ≤ back - out), abs_of_nonneg (by omega : (0 : ℤ) ≤ c - H),
    abs_of_nonneg (by omega : (0 : ℤ) ≤ back - vt), abs_of_nonneg (by omega : (0 : ℤ) ≤ ug - c)]
  ring

/-- **Residue invariance, unit to unit.** A route from unit `a` (source `(A_a + cs, V_U + vs)`)
via sub-band `b` (`BACK = V_T + 660 b + bk`, hairpin `H_I + h`) to unit `a'` (side line
`V_U + vt`, gate `A_{a'} + ug`) with `k` turns takes `2 · length - 5 k` generations; its residue
mod `30` depends only on the local offsets, not on `a, a', b` or the program. -/
theorem timeUp_mod (p : Program) (a a' b cs vs bk h vt ug k : ℤ) :
    (2 * (2 * (VT p + 660 * b + bk) - (VU p + vs) - (VU p + vt) + (A p a + cs) + (A p a' + ug)
        - 2 * (HI p + h)) - 5 * k) % 30 =
      (2 * (3288 + 2 * bk - vs - vt + cs + ug - 2 * h) - 5 * k) % 30 := by
  have := VT_mod p
  have := HI_mod p
  have := A_mod p a
  have := A_mod p a'
  unfold VU; omega

/-- **Residue invariance, unit to module.** A route from unit `a` to a port of module `r`
(port line `vp`, gate `U_r + ug`; the module has `v`-shift `0`): residue independent of
`a, r, b` and the program. -/
theorem timeDown_mod (p : Program) (a r cs vs h vp ug k : ℤ) :
    (2 * (vp - (VU p + vs) + (A p a + cs) + (U p r + ug) - 2 * (HI p + h)) - 5 * k) % 30 =
      (2 * (vp + 1644 - vs + cs + ug - 2 * h) - 5 * k) % 30 := by
  have := VT_mod p
  have := HI_mod p
  have := A_mod p a
  have := U_mod p r
  unfold VU; omega

/-- **Residue invariance, module to unit** (the answers): source `(U_r + cs, vs)` in module `r`. -/
theorem timeAns_mod (p : Program) (a r b cs vs bk h vt ug k : ℤ) :
    (2 * (2 * (VT p + 660 * b + bk) - vs - (VU p + vt) + (U p r + cs) + (A p a + ug)
        - 2 * (HI p + h)) - 5 * k) % 30 =
      (2 * (1644 + 2 * bk - vs - vt + cs + ug - 2 * h) - 5 * k) % 30 := by
  have := VT_mod p
  have := HI_mod p
  have := A_mod p a
  have := U_mod p r
  unfold VU; omega

/-- A hairpin moved by `-2` (`e ↦ e + 1`) lengthens the route by `4`, i.e. `8` generations. -/
theorem hairpin_step (us vs H vp ug : ℤ) :
    2 * (vp - vs + us + ug - 2 * (H - 2)) = 2 * (vp - vs + us + ug - 2 * H) + 8 := by ring

/-- `ρ* = 4` for even `r0`, `5` for odd `r0`. -/
def rhoStar (r0 : ℤ) : ℤ := 4 + r0 % 2

/-- The window rule `e = 2 (ρ* - r0) mod 15`. -/
def winE (r0 ρ : ℤ) : ℤ := 2 * (ρ - r0) % 15

/-- **Window rule.** If `r0 ≡ ρ (mod 2)` then `r0 + 8 e ≡ ρ (mod 30)` with
`e = 2 (ρ - r0) mod 15 ∈ [0, 14]`; in particular with `ρ = ρ*(r0)` every window input arrives at
residue `4` or `5`. -/
theorem window_rule (r0 ρ : ℤ) (h : (ρ - r0) % 2 = 0) :
    (r0 + 8 * winE r0 ρ) % 30 = ρ % 30 ∧ 0 ≤ winE r0 ρ ∧ winE r0 ρ ≤ 14 := by
  unfold winE; omega

/-- `ρ*(r0)` has the parity of `r0`, so the window rule applies to every residue `r0`. -/
theorem rhoStar_parity (r0 : ℤ) : (rhoStar r0 - r0) % 2 = 0 := by unfold rhoStar; omega

/-- `e_C = 9 q mod 15` is the window rule for the residue `r0_C = 4 + 18 q` of `C`. -/
theorem eC_eq_window (q : ℤ) : eC q = winE (4 + 18 * q) (rhoStar (4 + 18 * q)) := by
  unfold eC winE rhoStar; omega

/-- **`C` arrives at residue `4 + 2σ`** after its `e_C + 4σ + 15x` hairpin steps. -/
theorem C_residue (q : ℤ) : (4 + 18 * q + 8 * eCtot q) % 30 = (4 + 2 * sigma q) % 30 := by
  unfold eCtot eC sigma; omega

/-- Extra delays `G = 30 ⌈·/120⌉` of the INC continue keep every residue. -/
theorem G_mod (y : ℤ) : (30 * ceil120 y) % 30 = 0 := by omega

end LP

end LeanTheory.Life
