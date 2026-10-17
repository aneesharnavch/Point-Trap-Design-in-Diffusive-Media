module

public import TimeTraps.Analysis.PiecewiseDistributionTest
public import Mathlib.Analysis.Distribution.Distribution

@[expose] public section

/-! An interval-integrable signed density defines an actual continuous
distribution. Continuity follows from its L1 bound on bounded continuous
tests, composed with Mathlib's continuous test-function inclusion. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped Distributions BoundedContinuousFunction

noncomputable def piecewiseIntervalPairing (l r : ℝ) (hlr : l ≤ r) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume l r) : (ℝ →ᵇ ℝ) →L[ℝ] ℝ := by
  let T : (ℝ →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∫ x in l..r, f x * v x
      map_add' := by
        intro v w
        change (∫ x in l..r, f x * (v x + w x)) = _
        simp_rw [mul_add]
        exact intervalIntegral.integral_add
          (hf.mul_continuousOn v.continuous.continuousOn)
          (hf.mul_continuousOn w.continuous.continuousOn)
      map_smul' := by
        intro c v
        change (∫ x in l..r, f x * (c * v x)) = c * ∫ x in l..r, f x * v x
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring }
  refine T.mkContinuous (∫ x in l..r, ‖f x‖) ?_
  intro v
  change ‖∫ x in l..r, f x * v x‖ ≤ (∫ x in l..r, ‖f x‖) * ‖v‖
  calc
    _ ≤ ∫ x in l..r, ‖f x‖ * ‖v‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hlr
      · exact Filter.Eventually.of_forall fun x _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (v.norm_coe_le_norm x) (norm_nonneg _)
      · exact hf.norm.mul_const ‖v‖
    _ = _ := intervalIntegral.integral_mul_const _ _

theorem piecewiseIntervalPairing_apply (l r : ℝ) (hlr : l ≤ r) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume l r) (v : ℝ →ᵇ ℝ) :
    piecewiseIntervalPairing l r hlr f hf v = ∫ x in l..r, f x * v x := rfl

noncomputable def piecewiseIntervalDistribution (U : TopologicalSpace.Opens ℝ)
    (l r : ℝ) (hlr : l ≤ r) (f : ℝ → ℝ) (hf : IntervalIntegrable f volume l r) :
    𝓓'(U, ℝ) :=
  (piecewiseIntervalPairing l r hlr f hf).comp (TestFunction.toBoundedContinuousFunctionCLM ℝ)

theorem piecewiseIntervalDistribution_apply (U : TopologicalSpace.Opens ℝ)
    (l r : ℝ) (hlr : l ≤ r) (f : ℝ → ℝ) (hf : IntervalIntegrable f volume l r)
    (φ : 𝓓(U, ℝ)) :
    piecewiseIntervalDistribution U l r hlr f hf φ = ∫ x in l..r, f x * φ x := rfl

theorem piecewiseTestFunction_derivative (U : TopologicalSpace.Opens ℝ) (φ : 𝓓(U, ℝ)) :
    (⇑(TestFunction.lineDerivCLM ℝ (1 : ℝ) φ : 𝓓(U, ℝ))) = deriv φ := by
  funext x
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv

end TimeTraps.Analysis
