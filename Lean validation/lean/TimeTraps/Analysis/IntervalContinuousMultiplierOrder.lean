module

public import TimeTraps.Analysis.IntervalContinuousMultiplierAlgebra

@[expose] public section

/-! Physical pointwise lower bounds give quadratic-form bounds on all
length-L2 states. Positivity of a continuous coefficient on the compact
interval supplies a strictly positive lower bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace

variable {l r : ℝ}

theorem intervalContinuousCoefficient_pos_lower (hlr : l < r) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 < c x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc l r, m ≤ c x := by
  obtain ⟨x, hx, hm⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc l r).Nonempty from ⟨l, le_rfl, hlr.le⟩) hc
  exact ⟨c x, hp x hx, hm⟩

theorem intervalContinuousMultiplyL_lower (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (m : ℝ) (hm : ∀ x ∈ Icc l r, m ≤ c x)
    (f : IntervalSobolevL2 l r) :
    m * ‖f‖ ^ 2 ≤ inner ℝ (intervalContinuousMultiplyL c hc f) f := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) f f).const_mul m)
    (L2.integrable_inner (𝕜 := ℝ) (intervalContinuousMultiplyL c hc f) f)
  filter_upwards [intervalContinuousMultiplyL_coe c hc f,
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx hmem
  simp only [Real.inner_apply, hx]
  nlinarith [mul_le_mul_of_nonneg_right (hm x (Ioo_subset_Icc_self hmem)) (sq_nonneg (f x))]

theorem intervalContinuousMultiplyL_nonneg (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 ≤ c x)
    (f : IntervalSobolevL2 l r) : 0 ≤ inner ℝ (intervalContinuousMultiplyL c hc f) f := by
  simpa only [zero_mul] using intervalContinuousMultiplyL_lower c hc 0 hp f

theorem intervalContinuousMultiplyL_uniform_lower (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (f : IntervalSobolevL2 l r) :
    -‖intervalContinuousCoefficient c hc‖ * ‖f‖ ^ 2 ≤
      inner ℝ (intervalContinuousMultiplyL c hc f) f := by
  apply intervalContinuousMultiplyL_lower
  intro x hx
  have h := intervalContinuousCoefficient_bound c hc hx
  rw [Real.norm_eq_abs] at h
  exact (neg_le_neg h).trans (neg_abs_le (c x))

end TimeTraps.Analysis
