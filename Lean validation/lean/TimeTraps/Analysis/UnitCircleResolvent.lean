module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! The unit-circle real-part identity displayed in the finite cosine-sum
derivation. The nontrivial-root hypothesis makes the denominator nonzero. -/

namespace TimeTraps.Analysis

theorem unit_circle_two_div_one_sub_re (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    ((2 : ℂ) / (1 - z)).re = 1 := by
  have hnorm : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz, one_pow]
  have hden : Complex.normSq (1 - z) ≠ 0 :=
    mt Complex.normSq_eq_zero.mp (sub_ne_zero.mpr hne.symm)
  have hsq : Complex.normSq (1 - z) = 2 * (1 - z.re) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im] at hnorm ⊢
    nlinarith
  rw [Complex.div_re]
  have hr : (2 : ℂ).re = 2 := by norm_num
  have hi : (2 : ℂ).im = 0 := by norm_num
  rw [hr, hi, Complex.sub_re, Complex.one_re, zero_mul, zero_div, add_zero]
  exact (div_eq_one_iff_eq hden).mpr hsq.symm

end TimeTraps.Analysis
