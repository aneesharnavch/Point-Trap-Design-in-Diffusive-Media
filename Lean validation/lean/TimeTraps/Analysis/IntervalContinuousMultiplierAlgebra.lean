module

public import TimeTraps.Analysis.IntervalContinuousMultiplier

@[expose] public section

/-! Real continuous multipliers are symmetric, their compositions are
pointwise products, and a nowhere-zero coefficient has a bounded inverse
on the original physical L2 space. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace

variable {l r : ℝ}

theorem intervalContinuousMultiplyL_symmetric (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (f g : IntervalSobolevL2 l r) :
    inner ℝ (intervalContinuousMultiplyL c hc f) g =
      inner ℝ f (intervalContinuousMultiplyL c hc g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalContinuousMultiplyL_coe c hc f,
    intervalContinuousMultiplyL_coe c hc g] with x hf hg
  simp only [Real.inner_apply, hf, hg]
  ring

theorem intervalContinuousMultiplyL_comp (c d : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (hd : ContinuousOn d (Icc l r))
    (f : IntervalSobolevL2 l r) :
    intervalContinuousMultiplyL c hc (intervalContinuousMultiplyL d hd f) =
      intervalContinuousMultiplyL (fun x => c x * d x) (hc.mul hd) f := by
  apply Lp.ext
  filter_upwards [intervalContinuousMultiplyL_coe c hc (intervalContinuousMultiplyL d hd f),
    intervalContinuousMultiplyL_coe d hd f,
    intervalContinuousMultiplyL_coe (fun x => c x * d x) (hc.mul hd) f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, mul_assoc]

theorem intervalContinuousMultiplyL_one (f : IntervalSobolevL2 l r) :
    intervalContinuousMultiplyL (fun _ => (1 : ℝ)) continuousOn_const f = f := by
  apply Lp.ext
  filter_upwards [intervalContinuousMultiplyL_coe (fun _ => (1 : ℝ)) continuousOn_const f]
    with x hx
  simpa only [one_mul] using hx

theorem intervalContinuousMultiplyL_inverse_left (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (hn : ∀ x ∈ Icc l r, c x ≠ 0)
    (f : IntervalSobolevL2 l r) :
    intervalContinuousMultiplyL (fun x => (c x)⁻¹) (hc.inv₀ hn)
      (intervalContinuousMultiplyL c hc f) = f := by
  apply Lp.ext
  filter_upwards [intervalContinuousMultiplyL_coe (fun x => (c x)⁻¹) (hc.inv₀ hn)
      (intervalContinuousMultiplyL c hc f), intervalContinuousMultiplyL_coe c hc f,
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with x h₁ h₂ hx
  rw [h₁, h₂, ← mul_assoc, inv_mul_cancel₀ (hn x (Ioo_subset_Icc_self hx)), one_mul]

theorem intervalContinuousMultiplyL_inverse_right (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (hn : ∀ x ∈ Icc l r, c x ≠ 0)
    (f : IntervalSobolevL2 l r) :
    intervalContinuousMultiplyL c hc
      (intervalContinuousMultiplyL (fun x => (c x)⁻¹) (hc.inv₀ hn) f) = f := by
  apply Lp.ext
  filter_upwards [intervalContinuousMultiplyL_coe c hc
      (intervalContinuousMultiplyL (fun x => (c x)⁻¹) (hc.inv₀ hn) f),
    intervalContinuousMultiplyL_coe (fun x => (c x)⁻¹) (hc.inv₀ hn) f,
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with x h₁ h₂ hx
  rw [h₁, h₂, ← mul_assoc, mul_inv_cancel₀ (hn x (Ioo_subset_Icc_self hx)), one_mul]

noncomputable def intervalContinuousMultiplyEquiv (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (hn : ∀ x ∈ Icc l r, c x ≠ 0) :
    IntervalSobolevL2 l r ≃L[ℝ] IntervalSobolevL2 l r where
  toLinearEquiv := {
    toLinearMap := (intervalContinuousMultiplyL c hc).toLinearMap
    invFun := intervalContinuousMultiplyL (fun x => (c x)⁻¹) (hc.inv₀ hn)
    left_inv := intervalContinuousMultiplyL_inverse_left c hc hn
    right_inv := intervalContinuousMultiplyL_inverse_right c hc hn }
  continuous_toFun := (intervalContinuousMultiplyL c hc).continuous
  continuous_invFun := (intervalContinuousMultiplyL (fun x => (c x)⁻¹) (hc.inv₀ hn)).continuous

theorem intervalContinuousMultiplyL_bijective (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc l r)) (hn : ∀ x ∈ Icc l r, c x ≠ 0) :
    Function.Bijective (intervalContinuousMultiplyL c hc) :=
  (intervalContinuousMultiplyEquiv c hc hn).bijective

end TimeTraps.Analysis
