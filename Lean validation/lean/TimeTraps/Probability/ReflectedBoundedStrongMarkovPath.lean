module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPathCylinder

@[expose] public section

/-! Full finite-horizon future-path strong Markov law for the actual
reflected reference process. Every bounded Borel path functional is
permitted; its continuation law is independently constructed from a
fresh Brownian coordinate at the stopped spatial state. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

theorem reflectedMarkovFuturePath_stopping_map_eq
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (H : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (brownianCompletedMeasure.restrict A).map (reflectedMarkovFuturePath L hL D x H τ) =
      ((brownianCompletedMeasure.restrict A).prod brownianCompletedMeasure).map
        (reflectedMarkovContinuationPath L hL D x H τ) := by
  apply reflectedMarkovPath_measure_ext
  intro w
  rw [integral_map (reflectedMarkovFuturePath_measurable L hL D x H hτ).aemeasurable
    (reflectedMarkovPathProduct L H w).continuous.measurable.aestronglyMeasurable,
    integral_map (reflectedMarkovContinuationPath_measurable L hL D x H hτ).aemeasurable
      (reflectedMarkovPathProduct L H w).continuous.measurable.aestronglyMeasurable]
  exact reflectedMarkovPathProduct_setIntegral L hL D hD x H w hτ hA

def reflectedMarkovPathOperator (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0)
    (g : ReflectedMarkovPath L H → ℝ) (y : Icc (0 : ℝ) L) : ℝ :=
  ∫ ω, g (reflectedMarkovFreshPath L hL D H (y, ω)) ∂brownianCompletedMeasure

theorem reflectedMarkovPathOperator_measurable (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0)
    {g : ReflectedMarkovPath L H → ℝ} (hg : Measurable g) :
    Measurable (reflectedMarkovPathOperator L hL D H g) :=
  (hg.comp (reflectedMarkovFreshPath_measurable L hL D H)).stronglyMeasurable.integral_prod_right'.measurable

theorem reflectedMarkovPathOperator_bound (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0)
    {g : ReflectedMarkovPath L H → ℝ} {M : ℝ} (hb : ∀ p, |g p| ≤ M)
    (y : Icc (0 : ℝ) L) : |reflectedMarkovPathOperator L hL D H g y| ≤ M := by
  simpa only [reflectedMarkovPathOperator, Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := brownianCompletedMeasure)
      (f := fun ω => g (reflectedMarkovFreshPath L hL D H (y, ω))) (C := M)
      (Eventually.of_forall (fun ω => hb (reflectedMarkovFreshPath L hL D H (y, ω)))))

theorem reflectedMarkovFuturePath_test_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {g : ReflectedMarkovPath L H → ℝ} (hg : Measurable g)
    {M : ℝ} (hb : ∀ p, |g p| ≤ M) :
    Integrable (fun ω => g (reflectedMarkovFuturePath L hL D x H τ ω)) brownianCompletedMeasure := by
  apply (integrable_const M).mono'
    (hg.comp (reflectedMarkovFuturePath_measurable L hL D x H hτ)).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => hb _)

theorem reflectedMarkovContinuationPath_borel_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (ν : Measure BrownianCompletedSample) [IsFiniteMeasure ν]
    {g : ReflectedMarkovPath L H → ℝ} (hg : Measurable g)
    {M : ℝ} (hb : ∀ p, |g p| ≤ M) :
    Integrable (fun q => g (reflectedMarkovContinuationPath L hL D x H τ q))
      (ν.prod brownianCompletedMeasure) := by
  apply (integrable_const M).mono'
    (hg.comp (reflectedMarkovContinuationPath_measurable L hL D x H hτ)).aestronglyMeasurable
  exact Eventually.of_forall (fun q => hb _)

theorem reflectedMarkovFuturePath_borel_setIntegral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (H : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {g : ReflectedMarkovPath L H → ℝ} (hg : Measurable g)
    {M : ℝ} (hb : ∀ p, |g p| ≤ M)
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, g (reflectedMarkovFuturePath L hL D x H τ ω) ∂brownianCompletedMeasure) =
      ∫ ω in A, reflectedMarkovPathOperator L hL D H g
        (reflectedMarkovState L hL D x (τ ω) ω) ∂brownianCompletedMeasure := by
  calc
    _ = ∫ p, g p ∂(brownianCompletedMeasure.restrict A).map
        (reflectedMarkovFuturePath L hL D x H τ) :=
      (integral_map (reflectedMarkovFuturePath_measurable L hL D x H hτ).aemeasurable
        hg.aestronglyMeasurable).symm
    _ = ∫ p, g p ∂((brownianCompletedMeasure.restrict A).prod brownianCompletedMeasure).map
        (reflectedMarkovContinuationPath L hL D x H τ) :=
      congrArg (fun ν => ∫ p, g p ∂ν) (reflectedMarkovFuturePath_stopping_map_eq L hL D hD x H hτ hA)
    _ = _ := (integral_map (reflectedMarkovContinuationPath_measurable L hL D x H hτ).aemeasurable
      hg.aestronglyMeasurable).trans (integral_prod _
        (reflectedMarkovContinuationPath_borel_integrable L hL D x H hτ
          (brownianCompletedMeasure.restrict A) hg hb))

theorem reflectedMarkovFuturePath_strongMarkov
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (H : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {g : ReflectedMarkovPath L H → ℝ} (hg : Measurable g)
    {M : ℝ} (hb : ∀ p, |g p| ≤ M) :
    brownianCompletedMeasure[(fun ω => g (reflectedMarkovFuturePath L hL D x H τ ω)) |
      hτ.measurableSpace] =ᵐ[brownianCompletedMeasure]
        (fun ω => reflectedMarkovPathOperator L hL D H g
          (reflectedMarkovState L hL D x (τ ω) ω)) := by
  have hsm : StronglyMeasurable[hτ.measurableSpace]
      (fun ω => reflectedMarkovPathOperator L hL D H g
        (reflectedMarkovState L hL D x (τ ω) ω)) :=
    ((reflectedMarkovPathOperator_measurable L hL D H hg).comp
      (reflectedMarkovState_stopped_stronglyMeasurable L hL D x hτ).measurable).stronglyMeasurable
  have hi : Integrable
      (fun ω => reflectedMarkovPathOperator L hL D H g
        (reflectedMarkovState L hL D x (τ ω) ω)) brownianCompletedMeasure := by
    apply (integrable_const M).mono' (hsm.mono hτ.measurableSpace_le).aestronglyMeasurable
    exact Eventually.of_forall (fun ω => reflectedMarkovPathOperator_bound L hL D H hb _)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
    (reflectedMarkovFuturePath_test_integrable L hL D x H hτ hg hb) _ _
      hsm.aestronglyMeasurable).symm
  · exact fun _ _ _ => hi.integrableOn
  · exact fun _ hA _ => (reflectedMarkovFuturePath_borel_setIntegral L hL D hD x H hτ hg hb hA).symm

end TimeTraps.Probability

end
