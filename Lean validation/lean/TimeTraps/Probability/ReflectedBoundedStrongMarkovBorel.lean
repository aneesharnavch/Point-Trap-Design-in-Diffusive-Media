module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovBorelMeasure

@[expose] public section

/-! The actual reflected Gaussian transition law at finite stopping
times for every bounded Borel spatial test. The measurable transition
operator is the already constructed probability law, including time zero. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

def reflectedBorelTimeOperator (L D : ℝ) (h : ℝ≥0) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, g z ∂reflectedGaussianLaw L y (Real.toNNReal (2 * D * h.val))

theorem reflectedBorelTimeOperator_measurable (L D : ℝ) (h : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) : Measurable (reflectedBorelTimeOperator L D h g) :=
  reflectedGaussianLaw_integral_measurable L _ hg

theorem reflectedBorelTimeOperator_bound (L D : ℝ) (h : ℝ≥0)
    {g : ℝ → ℝ} {M : ℝ} (hb : ∀ y, |g y| ≤ M) (y : ℝ) :
    |reflectedBorelTimeOperator L D h g y| ≤ M :=
  reflectedGaussianLaw_integral_bound L y _ hb

theorem reflectedBorelTimeOperator_standard (L D : ℝ) (h : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) (y : ℝ) :
    reflectedBorelTimeOperator L D h g y =
      ∫ z, g (reflectedFold L (y + Real.sqrt (Real.toNNReal (2 * D * h.val) : ℝ) * z))
        ∂gaussianReal 0 1 := by
  unfold reflectedBorelTimeOperator
  rw [reflectedGaussianLaw_standard]
  exact integral_map ((reflectedFold_measurable L).comp
    (measurable_const.add (measurable_const.mul measurable_id))).aemeasurable hg.aestronglyMeasurable

theorem reflectedMarkovState_borel_stopped_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, |g y| ≤ M) :
    Integrable (fun ω => g (reflectedMarkovState L hL D x (τ ω) ω).val) brownianCompletedMeasure := by
  apply (integrable_const M).mono'
    (hg.comp (measurable_subtype_coe.comp
      ((reflectedMarkovState_stopped_stronglyMeasurable L hL D x hτ).mono
        hτ.measurableSpace_le).measurable)).aestronglyMeasurable
  exact Eventually.of_forall (fun _ => hb _)

theorem reflectedMarkovState_borel_condExp (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, |g y| ≤ M) :
    brownianCompletedMeasure[(fun ω => g (reflectedMarkovState L hL D x (τ ω + h) ω).val) |
      hτ.measurableSpace] =ᵐ[brownianCompletedMeasure]
        (fun ω => reflectedBorelTimeOperator L D h g (reflectedMarkovState L hL D x (τ ω) ω).val) := by
  have hm : StronglyMeasurable[hτ.measurableSpace] (fun ω =>
      reflectedBorelTimeOperator L D h g (reflectedMarkovState L hL D x (τ ω) ω).val) :=
    ((reflectedBorelTimeOperator_measurable L D h hg).comp
      (measurable_subtype_coe.comp
        (reflectedMarkovState_stopped_stronglyMeasurable L hL D x hτ).measurable)).stronglyMeasurable
  have hi : Integrable (fun ω => reflectedBorelTimeOperator L D h g
      (reflectedMarkovState L hL D x (τ ω) ω).val) brownianCompletedMeasure :=
    reflectedMarkovState_borel_stopped_integrable L hL D x hτ
      (reflectedBorelTimeOperator_measurable L D h hg) (reflectedBorelTimeOperator_bound L D h hb)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
    (reflectedMarkovState_borel_stopped_integrable L hL D x
      (reflectedMarkovStoppingTime_add hτ h) hg hb)
    (fun _ _ _ => hi.integrableOn) ?_ hm.aestronglyMeasurable).symm
  intro A hA _
  have hpoint (ω : BrownianCompletedSample) :
      reflectedBorelTimeOperator L D h g (reflectedMarkovState L hL D x (τ ω) ω).val =
      ∫ z, g (reflectedMarkovGaussianFuture L hL D x τ h (ω, z)) ∂gaussianReal 0 1 :=
    reflectedBorelTimeOperator_standard L D h hg (reflectedMarkovState L hL D x (τ ω) ω).val
  exact (integral_congr_ae (Eventually.of_forall hpoint)).trans
    (reflectedMarkovState_borel_setIntegral L hL D hD x hτ h hg hb hA).symm

theorem foldedTrajectory_completed_borel_stopped_stronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) {g : ℝ → ℝ} (hg : Measurable g) :
    StronglyMeasurable[hτ.measurableSpace]
      (fun ω => g (foldedTrajectory L D x brownianDyadicPath (τ ω) ω)) := by
  apply brownianCompletedStopped_stronglyMeasurable_congr hτ
    (hg.comp (measurable_subtype_coe.comp
      (reflectedMarkovState_stopped_stronglyMeasurable L hL D x hτ).measurable)).stronglyMeasurable
  exact (reflectedMarkovState_actual_ae L hL D x).mono (fun ω hω => congrArg g (hω (τ ω)).symm)

theorem foldedTrajectory_completed_borel_stopped_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hb : ∀ y, |g y| ≤ M) :
    Integrable (fun ω => g (foldedTrajectory L D x brownianDyadicPath (τ ω) ω)) brownianCompletedMeasure :=
  (reflectedMarkovState_borel_stopped_integrable L hL D x hτ hg hb).congr
    ((reflectedMarkovState_actual_ae L hL D x).mono (fun ω hω => congrArg g (hω (τ ω))))

theorem foldedTrajectory_completed_borel_strongMarkov
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ y, |g y| ≤ M) :
    brownianCompletedMeasure[(fun ω => g (foldedTrajectory L D x brownianDyadicPath (τ ω + h) ω)) |
      hτ.measurableSpace] =ᵐ[brownianCompletedMeasure]
        (fun ω => reflectedBorelTimeOperator L D h g
          (foldedTrajectory L D x brownianDyadicPath (τ ω) ω)) := by
  have he := reflectedMarkovState_actual_ae L hL D x
  exact (condExp_congr_ae (he.mono (fun ω hω => congrArg g (hω (τ ω + h)).symm))).trans
    ((reflectedMarkovState_borel_condExp L hL D hD x hτ h hg hb).trans
      (he.mono (fun ω hω => congrArg (reflectedBorelTimeOperator L D h g) (hω (τ ω)))))

end TimeTraps.Probability

end
