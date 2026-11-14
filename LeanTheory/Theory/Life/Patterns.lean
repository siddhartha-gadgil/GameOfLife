/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.LifeCert
public import LeanTheory.Theory.Life.Locality

/-!
# Basic patterns of the Game of Life

Definitions of the classes of basic patterns and a catalogue of named patterns with their
proved behaviour (research notes `N-05`, `N-06`). All statements are about Conway's rule
`conway` and the kernel evolution `Rule.evolve`.

## Classes

* `IsStillLife S`: `S` is nonempty and unchanged by one generation.
* `IsOscillator S p`: `S` returns to itself after `p ≥ 2` generations and not earlier.
* `IsSpaceship S p v`: after `p` generations `S` is its translate by `v ≠ 0`, and `S` is not a
  translate of itself after fewer generations.

Each class is invariant under translation (`IsStillLife.translate`, `IsOscillator.translate`,
`IsSpaceship.translate`), and the behaviour for all time follows from the definition
(`IsStillLife.evolve`, `IsOscillator.evolve_mul`, `IsOscillator.evolve_mod`,
`IsSpaceship.evolve_mul`).

## Catalogue (namespace `Pattern`)

Patterns are given as windows `ofRows 0 0 rows`, with the picture in the docstring (`O` alive;
`x` increases to the right and `y` downward; in `rows` the least significant bit is the leftmost
cell).

* Still lifes: `block`, `beehive`, `loaf`, `boat`, `pond`, `eater1`.
* Oscillators: `blinker` (2), `toad` (2), `beacon` (2), `trafficLight` (2), `pulsar` (3),
  `pentadecathlon` (15).
* Spaceships: `glider` (period 4, displacement `(1, 1)`), `lwss`, `mwss`, `hwss` (period 4,
  displacement `(-2, 0)`).

The proofs are evolution certificates (`life_cert`, `life_eval`); minimality of periods uses the
uniqueness of trimmed windows (`ofRows_ne`, `ofRows_ne_of_rows_ne`).

**Sanity.** `glider_evolve_mul_four` (the glider at all multiples of four generations),
`not_isStillLife_blinker` (the classes exclude something), `translate_ofRows`.
-/

@[expose] public section

namespace LeanTheory.Life

open Finset

/-- Translating a window translates its origin. -/
theorem translate_ofRows (a b x y : ℤ) (rows : List ℕ) :
    translate (a, b) (ofRows x y rows) = ofRows (x + a) (y + b) rows := by
  ext ⟨c, d⟩
  rw [mem_translate, mem_ofRows, mem_ofRows]
  have e1 : ((c, d) - (a, b) : Cell).1 - x = ((c, d) : Cell).1 - (x + a) := by
    simp only [Prod.fst_sub]
    omega
  have e2 : ((c, d) - (a, b) : Cell).2 - y = ((c, d) : Cell).2 - (y + b) := by
    simp only [Prod.snd_sub]
    omega
  rw [e1, e2]

/-! ### Classes of patterns -/

/-- A still life: a nonempty configuration unchanged by one generation. -/
def IsStillLife (S : Finset Cell) : Prop := S.Nonempty ∧ conway.step S = S

/-- An oscillator of period exactly `p ≥ 2`. -/
def IsOscillator (S : Finset Cell) (p : ℕ) : Prop :=
  2 ≤ p ∧ conway.evolve p S = S ∧ ∀ k, 0 < k → k < p → conway.evolve k S ≠ S

/-- A spaceship of period exactly `p` and displacement `v ≠ 0`: after `p` generations the
configuration is its translate by `v`, and after fewer generations it is not a translate of
itself at all. -/
def IsSpaceship (S : Finset Cell) (p : ℕ) (v : Cell) : Prop :=
  S.Nonempty ∧ v ≠ 0 ∧ 0 < p ∧ conway.evolve p S = translate v S ∧
    ∀ k, 0 < k → k < p → ∀ w, conway.evolve k S ≠ translate w S

/-- Translation is injective on configurations. -/
theorem translate_injective (v : Cell) : Function.Injective (translate v) := by
  intro S T h
  have h' := congrArg (translate (-v)) h
  rwa [translate_translate, translate_translate, neg_add_cancel, translate_zero,
    translate_zero] at h'

/-- A translate is nonempty iff the configuration is. -/
theorem translate_nonempty {v : Cell} {S : Finset Cell} :
    (translate v S).Nonempty ↔ S.Nonempty := by
  simp [translate]

/-- A still life stays as it is forever. -/
theorem IsStillLife.evolve {S : Finset Cell} (h : IsStillLife S) (n : ℕ) :
    conway.evolve n S = S := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Rule.evolve_succ, ih, h.2]

/-- A translate of a still life is a still life. -/
theorem IsStillLife.translate {S : Finset Cell} (h : IsStillLife S) (v : Cell) :
    IsStillLife (translate v S) :=
  ⟨translate_nonempty.2 h.1, by rw [Rule.step_translate_eq, h.2]⟩

/-- An oscillator returns to itself at every multiple of its period. -/
theorem IsOscillator.evolve_mul {S : Finset Cell} {p : ℕ} (h : IsOscillator S p) (k : ℕ) :
    conway.evolve (k * p) S = S :=
  conway.evolve_mul_of_evolve_eq h.2.1 k

/-- The state of an oscillator depends only on the generation modulo its period. -/
theorem IsOscillator.evolve_mod {S : Finset Cell} {p : ℕ} (h : IsOscillator S p) (n : ℕ) :
    conway.evolve n S = conway.evolve (n % p) S :=
  conway.evolve_mod_of_evolve_eq h.2.1 n

/-- A translate of an oscillator is an oscillator of the same period. -/
theorem IsOscillator.translate {S : Finset Cell} {p : ℕ} (h : IsOscillator S p) (v : Cell) :
    IsOscillator (translate v S) p := by
  refine ⟨h.1, by rw [Rule.evolve_translate, h.2.1], fun k hk0 hk he => ?_⟩
  rw [Rule.evolve_translate] at he
  exact h.2.2 k hk0 hk (translate_injective v he)

/-- A spaceship at every multiple of its period. -/
theorem IsSpaceship.evolve_mul {S : Finset Cell} {p : ℕ} {v : Cell} (h : IsSpaceship S p v)
    (k : ℕ) : conway.evolve (k * p) S = translate (k • v) S :=
  conway.evolve_mul_of_evolve_eq_translate h.2.2.2.1 k

/-- A translate of a spaceship is a spaceship with the same period and displacement. -/
theorem IsSpaceship.translate {S : Finset Cell} {p : ℕ} {v : Cell} (h : IsSpaceship S p v)
    (u : Cell) : IsSpaceship (translate u S) p v := by
  refine ⟨translate_nonempty.2 h.1, h.2.1, h.2.2.1, ?_, fun k hk0 hk w he => ?_⟩
  · rw [Rule.evolve_translate, h.2.2.2.1, translate_translate, translate_translate, add_comm]
  · rw [Rule.evolve_translate, translate_translate, add_comm, ← translate_translate] at he
    exact h.2.2.2.2 k hk0 hk w (translate_injective u he)

/-! ### The catalogue -/

namespace Pattern

/-- The block, a two-by-two square. 4 cells.
```
OO
OO
```
-/
def block : Finset Cell := ofRows 0 0 [3, 3]

/-- The block is a still life. -/
theorem block_isStillLife : IsStillLife block :=
  ⟨ofRows_nonempty rfl 0 0, by rw [← Rule.evolve_one]; life_cert⟩

/-- The beehive. 6 cells.
```
.OO.
O..O
.OO.
```
-/
def beehive : Finset Cell := ofRows 0 0 [6, 9, 6]

/-- The beehive is a still life. -/
theorem beehive_isStillLife : IsStillLife beehive :=
  ⟨ofRows_nonempty rfl 0 0, by rw [← Rule.evolve_one]; life_cert⟩

/-- The loaf. 7 cells.
```
.OO.
O..O
.O.O
..O.
```
-/
def loaf : Finset Cell := ofRows 0 0 [6, 9, 10, 4]

/-- The loaf is a still life. -/
theorem loaf_isStillLife : IsStillLife loaf :=
  ⟨ofRows_nonempty rfl 0 0, by rw [← Rule.evolve_one]; life_cert⟩

/-- The boat. 5 cells.
```
OO.
O.O
.O.
```
-/
def boat : Finset Cell := ofRows 0 0 [3, 5, 2]

/-- The boat is a still life. -/
theorem boat_isStillLife : IsStillLife boat :=
  ⟨ofRows_nonempty rfl 0 0, by rw [← Rule.evolve_one]; life_cert⟩

/-- The pond. 8 cells.
```
.OO.
O..O
O..O
.OO.
```
-/
def pond : Finset Cell := ofRows 0 0 [6, 9, 9, 6]

/-- The pond is a still life. -/
theorem pond_isStillLife : IsStillLife pond :=
  ⟨ofRows_nonempty rfl 0 0, by rw [← Rule.evolve_one]; life_cert⟩

/-- Eater 1 (the fishhook). 7 cells.
```
OO..
O.O.
..O.
..OO
```
-/
def eater1 : Finset Cell := ofRows 0 0 [3, 5, 4, 12]

/-- The eater 1 is a still life. -/
theorem eater1_isStillLife : IsStillLife eater1 :=
  ⟨ofRows_nonempty rfl 0 0, by rw [← Rule.evolve_one]; life_cert⟩

/-- The blinker, in its horizontal phase. 3 cells.
```
OOO
```
-/
def blinker : Finset Cell := ofRows 0 0 [7]

/-- The blinker is an oscillator of period exactly 2. -/
theorem blinker_isOscillator : IsOscillator blinker 2 := by
  refine ⟨by norm_num, by life_cert, fun k hk0 hk => ?_⟩
  interval_cases k
  life_eval
  exact ofRows_ne rfl rfl (by simp)

/-- The toad. 6 cells.
```
.OOO
OOO.
```
-/
def toad : Finset Cell := ofRows 0 0 [14, 7]

/-- The toad is an oscillator of period exactly 2. -/
theorem toad_isOscillator : IsOscillator toad 2 := by
  refine ⟨by norm_num, by life_cert, fun k hk0 hk => ?_⟩
  interval_cases k
  life_eval
  exact ofRows_ne rfl rfl (by simp)

/-- The beacon. 8 cells.
```
OO..
OO..
..OO
..OO
```
-/
def beacon : Finset Cell := ofRows 0 0 [3, 3, 12, 12]

/-- The beacon is an oscillator of period exactly 2. -/
theorem beacon_isOscillator : IsOscillator beacon 2 := by
  refine ⟨by norm_num, by life_cert, fun k hk0 hk => ?_⟩
  interval_cases k
  life_eval
  exact ofRows_ne rfl rfl (by simp)

/-- The traffic light: four blinkers around an empty centre (pattern data from the
LifeWiki page "Traffic light", RLE `2b3o2$o5bo$o5bo$o5bo2$2b3o!`). 12 cells.
```
..OOO..
.......
O.....O
O.....O
O.....O
.......
..OOO..
```
-/
def trafficLight : Finset Cell := ofRows 0 0 [28, 0, 65, 65, 65, 0, 28]

/-- The traffic light is an oscillator of period exactly 2. -/
theorem trafficLight_isOscillator : IsOscillator trafficLight 2 := by
  refine ⟨by norm_num, by life_cert, fun k hk0 hk => ?_⟩
  interval_cases k
  life_eval
  exact ofRows_ne rfl rfl (by simp)

/-- The pulsar. 48 cells.
```
..OOO...OOO..
.............
O....O.O....O
O....O.O....O
O....O.O....O
..OOO...OOO..
.............
..OOO...OOO..
O....O.O....O
O....O.O....O
O....O.O....O
.............
..OOO...OOO..
```
-/
def pulsar : Finset Cell :=
  ofRows 0 0 [1820, 0, 4257, 4257, 4257, 1820, 0, 1820, 4257, 4257, 4257, 0, 1820]

/-- The pulsar is an oscillator of period exactly 3. -/
theorem pulsar_isOscillator : IsOscillator pulsar 3 := by
  refine ⟨by norm_num, by life_cert, fun k hk0 hk => ?_⟩
  interval_cases k <;> (life_eval; exact ofRows_ne rfl rfl (by simp))

/-- The pentadecathlon. 12 cells.
```
..O....O..
OO.OOOO.OO
..O....O..
```
-/
def pentadecathlon : Finset Cell := ofRows 0 0 [132, 891, 132]

/-- The pentadecathlon is an oscillator of period exactly 15. -/
theorem pentadecathlon_isOscillator : IsOscillator pentadecathlon 15 := by
  refine ⟨by norm_num, by life_cert, fun k hk0 hk => ?_⟩
  interval_cases k <;> (life_eval; exact ofRows_ne rfl rfl (by simp))

/-- The glider, in the phase that travels to the right and downward. 5 cells.
```
.O.
..O
OOO
```
-/
def glider : Finset Cell := ofRows 0 0 [2, 4, 7]

/-- The glider is a spaceship of period exactly 4: after 4 generations it has moved
one cell to the right and one cell down, and it is not a translate of itself earlier. -/
theorem glider_isSpaceship : IsSpaceship glider 4 (1, 1) := by
  refine ⟨ofRows_nonempty rfl 0 0, by simp, by norm_num, ?_, fun k hk0 hk w => ?_⟩
  · rw [glider, translate_ofRows]
    life_cert
  · obtain ⟨a, b⟩ := w
    rw [glider, translate_ofRows]
    interval_cases k <;> (life_eval; exact ofRows_ne_of_rows_ne rfl rfl (by simp))

/-- The lightweight spaceship, travelling to the left. 9 cells.
```
.O..O
O....
O...O
OOOO.
```
-/
def lwss : Finset Cell := ofRows 0 0 [18, 1, 17, 15]

/-- The lightweight spaceship is a spaceship of period exactly 4: after 4 generations it has moved
two cells to the left, and it is not a translate of itself earlier. -/
theorem lwss_isSpaceship : IsSpaceship lwss 4 (-2, 0) := by
  refine ⟨ofRows_nonempty rfl 0 0, by simp, by norm_num, ?_, fun k hk0 hk w => ?_⟩
  · rw [lwss, translate_ofRows]
    life_cert
  · obtain ⟨a, b⟩ := w
    rw [lwss, translate_ofRows]
    interval_cases k <;> (life_eval; exact ofRows_ne_of_rows_ne rfl rfl (by simp))

/-- The middleweight spaceship, travelling to the left. 11 cells.
```
...O..
.O...O
O.....
O....O
OOOOO.
```
-/
def mwss : Finset Cell := ofRows 0 0 [8, 34, 1, 33, 31]

/-- The middleweight spaceship is a spaceship of period exactly 4: after 4 generations it has moved
two cells to the left, and it is not a translate of itself earlier. -/
theorem mwss_isSpaceship : IsSpaceship mwss 4 (-2, 0) := by
  refine ⟨ofRows_nonempty rfl 0 0, by simp, by norm_num, ?_, fun k hk0 hk w => ?_⟩
  · rw [mwss, translate_ofRows]
    life_cert
  · obtain ⟨a, b⟩ := w
    rw [mwss, translate_ofRows]
    interval_cases k <;> (life_eval; exact ofRows_ne_of_rows_ne rfl rfl (by simp))

/-- The heavyweight spaceship, travelling to the left. 13 cells.
```
...OO..
.O....O
O......
O.....O
OOOOOO.
```
-/
def hwss : Finset Cell := ofRows 0 0 [24, 66, 1, 65, 63]

/-- The heavyweight spaceship is a spaceship of period exactly 4: after 4 generations it has moved
two cells to the left, and it is not a translate of itself earlier. -/
theorem hwss_isSpaceship : IsSpaceship hwss 4 (-2, 0) := by
  refine ⟨ofRows_nonempty rfl 0 0, by simp, by norm_num, ?_, fun k hk0 hk w => ?_⟩
  · rw [hwss, translate_ofRows]
    life_cert
  · obtain ⟨a, b⟩ := w
    rw [hwss, translate_ofRows]
    interval_cases k <;> (life_eval; exact ofRows_ne_of_rows_ne rfl rfl (by simp))

/-! ### Sanity -/

/-- **Sanity** (all time): the glider after `4 k` generations is the glider moved `k` cells to
the right and `k` cells down. -/
theorem glider_evolve_mul_four (k : ℕ) :
    conway.evolve (k * 4) glider = translate ((k : ℤ), (k : ℤ)) glider := by
  rw [glider_isSpaceship.evolve_mul]
  simp

/-- **Sanity** (the classes exclude something): the blinker is not a still life. -/
theorem not_isStillLife_blinker : ¬ IsStillLife blinker := by
  intro h
  have h1 := blinker_isOscillator.2.2 1 (by norm_num) (by norm_num)
  exact h1 h.2

end Pattern

end LeanTheory.Life
