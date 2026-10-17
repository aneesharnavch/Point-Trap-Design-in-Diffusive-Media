module

public import TimeTraps.Probability.ReflectedGaussianSemigroup
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! The folded Gaussian laws form actual measurable probability kernels.
Their composition is exactly addition of variances. On the ambient real
line the zero kernel is deterministic folding; at every point of [0,L]
it is the identity Dirac law, as required for the reflected state space. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem reflectedGaussianLaw_measurable (L : ℝ) (v : ℝ≥0) :
    Measurable (fun x => reflectedGaussianLaw L x v) := by
  let F : ℝ × ℝ → ℝ := fun p => reflectedFold L (p.1 + p.2)
  have hF : Measurable F := (reflectedFold_measurable L).comp (measurable_fst.add measurable_snd)
  have he : (fun x => reflectedGaussianLaw L x v) =
      (fun x => ((gaussianReal 0 v).map (Prod.mk x)).map F) := by
    funext x
    rw [Measure.map_map hF (show Measurable (Prod.mk x) from measurable_const.prodMk measurable_id)]
    exact reflectedGaussianLaw_centered L x v
  rw [he]
  exact (Measure.measurable_map F hF).comp (Measurable.map_prodMk_left (ν := gaussianReal 0 v))

def reflectedGaussianTransition (L : ℝ) (v : ℝ≥0) : Kernel ℝ ℝ where
  toFun x := reflectedGaussianLaw L x v
  measurable' := reflectedGaussianLaw_measurable L v

instance reflectedGaussianTransition_isMarkovKernel (L : ℝ) (v : ℝ≥0) :
    IsMarkovKernel (reflectedGaussianTransition L v) where
  isProbabilityMeasure x := reflectedGaussianLaw_isProbabilityMeasure L x v

theorem reflectedGaussianTransition_apply (L x : ℝ) (v : ℝ≥0) :
    reflectedGaussianTransition L v x = reflectedGaussianLaw L x v := rfl

theorem reflectedGaussianTransition_zero (L : ℝ) :
    reflectedGaussianTransition L 0 = Kernel.deterministic (reflectedFold L) (reflectedFold_measurable L) := by
  apply Kernel.ext
  intro x
  exact reflectedGaussianLaw_zero L x

theorem reflectedGaussianTransition_zero_apply (L : ℝ) (hL : 0 < L) {x : ℝ}
    (hx : x ∈ Icc 0 L) : reflectedGaussianTransition L 0 x = Measure.dirac x := by
  rw [reflectedGaussianTransition_apply, reflectedGaussianLaw_zero, reflectedFold_eq_self L hL x hx]

theorem reflectedGaussianTransition_comp (L : ℝ) (hL : 0 < L) (v₁ v₂ : ℝ≥0) :
    (reflectedGaussianTransition L v₂) ∘ₖ (reflectedGaussianTransition L v₁) =
      reflectedGaussianTransition L (v₁ + v₂) := by
  apply Kernel.ext
  intro x
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hgi : Integrable (A.indicator (fun _ : ℝ => (1 : ℝ)))
      (((reflectedGaussianTransition L v₂) ∘ₖ (reflectedGaussianTransition L v₁)) x) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hb (y : ℝ) : |A.indicator (fun _ : ℝ => (1 : ℝ)) y| ≤ 1 := by
    by_cases hy : y ∈ A <;> simp [hy]
  have he := (Kernel.integral_comp hgi).trans
    (reflectedGaussianLaw_integral_comp L hL x v₁ v₂ (measurable_const.indicator hA) hb)
  have hi (μ : Measure ℝ) : (∫ z, A.indicator (fun _ : ℝ => (1 : ℝ)) z ∂μ) = (μ A).toReal := by
    simpa only [smul_eq_mul, mul_one, measureReal_def] using integral_indicator_const (μ := μ) (1 : ℝ) hA
  exact (hi _).symm.trans (he.trans (hi _))

end TimeTraps.Probability

end
