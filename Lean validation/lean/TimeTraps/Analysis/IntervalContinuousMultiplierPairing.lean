module

public import TimeTraps.Analysis.IntervalContinuousMultiplierOrder
public import TimeTraps.Analysis.IntervalWeightedState

@[expose] public section

/-! Multiplier pairings retain the actual physical state and derivative
integrals. The square-root speed inclusion has exactly the weighted
quadratic mass on the full original H1 space. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {l r : ℝ}

theorem intervalContinuousMultiplyL_state_inner (hlr : l < r) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (u v : IntervalSobolevSpace l r) :
    inner ℝ (intervalContinuousMultiplyL c hc u.state) v.state =
      ∫ x in l..r, c x * u.representative hlr x * v.representative hlr x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [intervalContinuousMultiplyL_coe c hc u.state,
    (u.representative_spec hlr).2.1, (v.representative_spec hlr).2.1] with x hc' hu hv
  simp only [Real.inner_apply, hc', hu, hv]

theorem intervalContinuousMultiplyL_gradient_inner (hlr : l < r) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (u v : IntervalSobolevSpace l r) :
    inner ℝ (intervalContinuousMultiplyL c hc u.gradient) v.gradient =
      ∫ x in l..r, c x * deriv (u.representative hlr) x * deriv (v.representative hlr) x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [intervalContinuousMultiplyL_coe c hc u.gradient,
    (u.representative_spec hlr).2.2, (v.representative_spec hlr).2.2] with x hc' hu hv
  simp only [Real.inner_apply, hc', hu, hv]

theorem intervalWeightedStateL_norm_sq_pairing (hlr : l < r) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 ≤ w x)
    (u : IntervalSobolevSpace l r) :
    ‖intervalWeightedStateL w hw u‖ ^ 2 =
      inner ℝ (intervalContinuousMultiplyL w hw u.state) u.state := by
  rw [← real_inner_self_eq_norm_sq, intervalWeightedStateL_inner hlr w hw hp,
    intervalContinuousMultiplyL_state_inner hlr w hw]

theorem intervalWeightedStateL_lower (hlr : l < r) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 ≤ w x)
    (m : ℝ) (hm : ∀ x ∈ Icc l r, m ≤ w x) (u : IntervalSobolevSpace l r) :
    m * ‖u.state‖ ^ 2 ≤ ‖intervalWeightedStateL w hw u‖ ^ 2 := by
  rw [intervalWeightedStateL_norm_sq_pairing hlr w hw hp]
  exact intervalContinuousMultiplyL_lower w hw m hm u.state

end TimeTraps.Analysis
