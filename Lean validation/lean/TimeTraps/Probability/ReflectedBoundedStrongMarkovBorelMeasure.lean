module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovBorelData

@[expose] public section

/-! The stopped future distribution, tested on each event of the stopped
past, equals a fresh Gaussian continuation. Finite-measure uniqueness
extends the continuous-test identity to every bounded Borel test. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

def reflectedMarkovGaussianFuture (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (τ : BrownianCompletedSample → ℝ≥0) (h : ℝ≥0) (p : BrownianCompletedSample × ℝ) : ℝ :=
  reflectedFold L ((reflectedMarkovState L hL D x (τ p.1) p.1).val +
    Real.sqrt (Real.toNNReal (2 * D * h.val) : ℝ) * p.2)

theorem reflectedMarkovGaussianFuture_measurable (L : ℝ) (hL : 0 < L) (D x : ℝ)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0) :
    Measurable (reflectedMarkovGaussianFuture L hL D x τ h) := by
  have hm := measurable_subtype_coe.comp
    ((reflectedMarkovState_stopped_stronglyMeasurable L hL D x hτ).mono hτ.measurableSpace_le).measurable
  exact (reflectedFold_measurable L).comp
    ((hm.comp measurable_fst).add (measurable_const.mul measurable_snd))

theorem reflectedMarkovGaussianFuture_integrable (L : ℝ) (hL : 0 < L) (D x : ℝ)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0)
    (ν : Measure BrownianCompletedSample) [IsFiniteMeasure ν]
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, |g y| ≤ M) :
    Integrable (fun p => g (reflectedMarkovGaussianFuture L hL D x τ h p))
      (ν.prod (gaussianReal 0 1)) := by
  apply (integrable_const M).mono'
    (hg.comp (reflectedMarkovGaussianFuture_measurable L hL D x hτ h)).aestronglyMeasurable
  exact Eventually.of_forall (fun p => hb _)

theorem reflectedMarkovState_stopping_map_eq (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0)
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (brownianCompletedMeasure.restrict A).map
      (fun ω => (reflectedMarkovState L hL D x (τ ω + h) ω).val) =
      ((brownianCompletedMeasure.restrict A).prod (gaussianReal 0 1)).map
        (reflectedMarkovGaussianFuture L hL D x τ h) := by
  have hY : Measurable (fun ω => (reflectedMarkovState L hL D x (τ ω + h) ω).val) :=
    measurable_subtype_coe.comp
      ((reflectedMarkovState_stopped_stronglyMeasurable L hL D x
        (reflectedMarkovStoppingTime_add hτ h)).mono
          (reflectedMarkovStoppingTime_add hτ h).measurableSpace_le).measurable
  have hG := reflectedMarkovGaussianFuture_measurable L hL D x hτ h
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hY.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    integral_map hG.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    integral_prod _ (reflectedMarkovGaussianFuture_integrable L hL D x hτ h
      (brownianCompletedMeasure.restrict A) f.continuous.measurable
        (fun y => f.norm_coe_le_norm y))]
  calc
    _ = ∫ ω in A, reflectedMarkovObservation L hL D x
        (reflectedFellerTimeOperator L hL D h.val (reflectedMarkovTestRestrict L f)) (τ ω) ω
          ∂brownianCompletedMeasure :=
      (reflectedMarkovObservation_stopping_setIntegral L hL D hD x
        (reflectedMarkovTestRestrict L f) h hτ hA).symm
    _ = _ := integral_congr_ae (Eventually.of_forall (fun ω =>
      reflectedMarkovTestRestrict_gaussian L hL D x f h (τ ω) ω))

theorem reflectedMarkovState_borel_setIntegral (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, |g y| ≤ M)
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, g (reflectedMarkovState L hL D x (τ ω + h) ω).val ∂brownianCompletedMeasure) =
      ∫ ω in A, (∫ z, g (reflectedMarkovGaussianFuture L hL D x τ h (ω, z)) ∂gaussianReal 0 1)
        ∂brownianCompletedMeasure := by
  have hY : Measurable (fun ω => (reflectedMarkovState L hL D x (τ ω + h) ω).val) :=
    measurable_subtype_coe.comp
      ((reflectedMarkovState_stopped_stronglyMeasurable L hL D x
        (reflectedMarkovStoppingTime_add hτ h)).mono
          (reflectedMarkovStoppingTime_add hτ h).measurableSpace_le).measurable
  calc
    _ = ∫ y, g y ∂(brownianCompletedMeasure.restrict A).map
        (fun ω => (reflectedMarkovState L hL D x (τ ω + h) ω).val) :=
      (integral_map hY.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂((brownianCompletedMeasure.restrict A).prod (gaussianReal 0 1)).map
        (reflectedMarkovGaussianFuture L hL D x τ h) :=
      congrArg (fun μ => ∫ y, g y ∂μ) (reflectedMarkovState_stopping_map_eq L hL D hD x hτ h hA)
    _ = _ := (integral_map (reflectedMarkovGaussianFuture_measurable L hL D x hτ h).aemeasurable
      hg.aestronglyMeasurable).trans
        (integral_prod _ (reflectedMarkovGaussianFuture_integrable L hL D x hτ h
          (brownianCompletedMeasure.restrict A) hg hb))

end TimeTraps.Probability

end
