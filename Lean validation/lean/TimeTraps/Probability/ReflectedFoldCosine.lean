module

public import TimeTraps.Probability.ReflectedFoldAffine
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-! The Neumann cosine modes are exactly invariant under triangular folding.
The identity holds at every real point, including all fold corners. -/

namespace TimeTraps.Probability

theorem reflectedFold_cosine (L : ℝ) (hL : 0 < L) (n : ℕ) (z : ℝ) :
    Real.cos (((n : ℝ) * Real.pi / L) * reflectedFold L z) =
      Real.cos (((n : ℝ) * Real.pi / L) * z) := by
  rw [reflectedFold_round]
  let k : ℤ := round ((2 * L)⁻¹ * z)
  have ha (a y : ℝ) : Real.cos (a * |y|) = Real.cos (a * y) := by
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
    · rw [abs_of_neg (lt_of_not_ge hy), mul_neg, Real.cos_neg]
  rw [ha]
  have he : ((n : ℝ) * Real.pi / L) * (z - (k : ℝ) * (2 * L)) =
      ((n : ℝ) * Real.pi / L) * z - ((k * (n : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp
  change Real.cos (((n : ℝ) * Real.pi / L) * (z - (k : ℝ) * (2 * L))) = _
  rw [he, Real.cos_sub_int_mul_two_pi]

end TimeTraps.Probability
