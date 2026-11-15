module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

example (x y : ℤ) (h : x ≤ y) : |y - x| + |x - y| = 2 * (y - x) := by omega
