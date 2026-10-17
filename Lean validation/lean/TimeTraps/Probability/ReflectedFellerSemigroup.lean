module

public import TimeTraps.Probability.ReflectedFellerContinuity
public import TimeTraps.Probability.ReflectedGaussianSemigroup

@[expose] public section

/-! The continuous-function operators satisfy the actual Gaussian
Chapman--Kolmogorov composition law, preserve order, and have norm at most
one. Composition uses the independently proved kernel integral identity. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem reflectedFellerOperator_extension_kernel (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    reflectedFellerExtension L hL (reflectedFellerOperator L hL v f) x =
      ∫ y, reflectedFellerExtension L hL f y ∂reflectedGaussianLaw L x v := by
  have h := reflectedFellerOperator_kernel L hL v f (reflectedIntervalFold L hL x)
  change reflectedFellerExtension L hL (reflectedFellerOperator L hL v f) x =
    ∫ y, reflectedFellerExtension L hL f y ∂reflectedGaussianLaw L (reflectedFold L x) v at h
  rwa [← reflectedGaussianLaw_fold_start L hL x v] at h

theorem reflectedFellerOperator_comp (L : ℝ) (hL : 0 < L) (v₁ v₂ : ℝ≥0) :
    (reflectedFellerOperator L hL v₁).comp (reflectedFellerOperator L hL v₂) =
      reflectedFellerOperator L hL (v₁ + v₂) := by
  ext f x
  change reflectedFellerOperator L hL v₁ (reflectedFellerOperator L hL v₂ f) x = _
  rw [reflectedFellerOperator_kernel]
  simp_rw [reflectedFellerOperator_extension_kernel]
  rw [reflectedGaussianLaw_integral_comp L hL x.val v₁ v₂
    (reflectedFellerExtension L hL f).continuous.measurable (fun y =>
      show |reflectedFellerExtension L hL f y| ≤ ‖f‖ from reflectedFellerExtension_bound L hL f y)]
  exact (reflectedFellerOperator_kernel L hL (v₁ + v₂) f x).symm

theorem reflectedFellerOperator_identity (L : ℝ) (hL : 0 < L) :
    reflectedFellerOperator L hL 0 = ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) L, ℝ) := by
  apply ContinuousLinearMap.ext
  intro f
  exact reflectedFellerOperator_zero L hL f

theorem reflectedFellerOperator_norm_le_one (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    ‖reflectedFellerOperator L hL v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using reflectedFellerOperator_contraction L hL v f

theorem reflectedFellerOperator_monotone (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    {f g : C(Icc (0 : ℝ) L, ℝ)} (hfg : ∀ x, f x ≤ g x) (x : Icc (0 : ℝ) L) :
    reflectedFellerOperator L hL v f x ≤ reflectedFellerOperator L hL v g x := by
  have h := reflectedFellerOperator_nonneg L hL v (f := g - f)
    (fun y => sub_nonneg.mpr (hfg y)) x
  rw [map_sub] at h
  exact sub_nonneg.mp h

end TimeTraps.Probability
