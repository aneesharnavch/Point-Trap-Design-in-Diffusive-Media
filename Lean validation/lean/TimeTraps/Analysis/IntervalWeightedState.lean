module

public import TimeTraps.Analysis.IntervalContinuousMultiplierAlgebra
public import TimeTraps.Analysis.IntervalSobolevCompactL2
public import TimeTraps.Analysis.IntervalSobolevDense

@[expose] public section

/-! The actual speed-weighted state inclusion is represented unitarily in
ordinary L2 by multiplying the physical state by sqrt(w). Its inner product
is exactly the physical integral against w, and it is compact, injective
and dense for every strictly positive continuous speed. No spatial
derivative of the speed is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {l r : ℝ}

noncomputable def intervalWeightedStateL (w : ℝ → ℝ) (hw : ContinuousOn w (Icc l r)) :
    IntervalSobolevSpace l r →L[ℝ] IntervalSobolevL2 l r :=
  (intervalContinuousMultiplyL (fun x => Real.sqrt (w x)) hw.sqrt).comp (stateL l r)

theorem intervalWeightedStateL_coe (w : ℝ → ℝ) (hw : ContinuousOn w (Icc l r))
    (u : IntervalSobolevSpace l r) :
    intervalWeightedStateL w hw u =ᵐ[volume.restrict (Ioo l r)]
      (fun x => Real.sqrt (w x) * u.state x) :=
  intervalContinuousMultiplyL_coe (fun x => Real.sqrt (w x)) hw.sqrt u.state

theorem intervalWeightedStateL_inner (hlr : l < r) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 ≤ w x)
    (u v : IntervalSobolevSpace l r) :
    inner ℝ (intervalWeightedStateL w hw u) (intervalWeightedStateL w hw v) =
      ∫ x in l..r, w x * u.representative hlr x * v.representative hlr x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le hlr.le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [intervalWeightedStateL_coe w hw u, intervalWeightedStateL_coe w hw v,
    (u.representative_spec hlr).2.1, (v.representative_spec hlr).2.1,
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hu hv hU hV hx
  simp only [Real.inner_apply, hu, hv, hU, hV]
  calc
    _ = (Real.sqrt (w x)) ^ 2 * u.representative hlr x * v.representative hlr x := by ring
    _ = _ := by rw [Real.sq_sqrt (hp x (Ioo_subset_Icc_self hx))]

theorem intervalWeightedStateL_norm_sq (hlr : l < r) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 ≤ w x)
    (u : IntervalSobolevSpace l r) :
    ‖intervalWeightedStateL w hw u‖ ^ 2 =
      ∫ x in l..r, w x * (u.representative hlr x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, intervalWeightedStateL_inner hlr w hw hp]
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem intervalWeightedStateL_injective (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 < w x) :
    Function.Injective (intervalWeightedStateL w hw) :=
  (intervalContinuousMultiplyL_bijective (fun x => Real.sqrt (w x)) hw.sqrt
    (fun x hx => (Real.sqrt_pos.2 (hp x hx)).ne')).1.comp (fun _ _ h => ext_state h)

theorem intervalWeightedStateL_compact (hlr : l < r) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc l r)) : IsCompactOperator (intervalWeightedStateL w hw) :=
  (stateL_isCompact hlr).clm_comp (intervalContinuousMultiplyL (fun x => Real.sqrt (w x)) hw.sqrt)

theorem intervalWeightedStateL_denseRange (hlr : l < r) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc l r)) (hp : ∀ x ∈ Icc l r, 0 < w x) :
    DenseRange (intervalWeightedStateL w hw) := by
  exact ((intervalContinuousMultiplyL_bijective (fun x => Real.sqrt (w x)) hw.sqrt
    (fun x hx => (Real.sqrt_pos.2 (hp x hx)).ne')).2.denseRange).comp
      (stateL_denseRange hlr)
      (intervalContinuousMultiplyL (fun x => Real.sqrt (w x)) hw.sqrt).continuous

end TimeTraps.Analysis
