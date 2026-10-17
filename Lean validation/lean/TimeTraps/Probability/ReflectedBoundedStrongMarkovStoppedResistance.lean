module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovStoppedTimeChange
public import TimeTraps.Probability.ReflectedBoundedStrongMarkovResistance

@[expose] public section

/-! The actual diffusion in the original medium is strong Markov in
its explicit inverse-clock Brownian filtration, for every finite physical
stopping time and every bounded Borel spatial test. The transition is the
independently defined actual path expectation, with the original medium
unchanged. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceInversePath_sampled_isStoppingTime (A : IntervalMedium) (x : ℝ)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (reversibleResistanceFiltration A x) (fun ω => (σ ω : WithTop ℝ≥0))) :
    IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (reversibleResistanceInversePath A x (σ ω) ω : WithTop ℝ≥0)) :=
  brownianInverseClock_sampled_isStoppingTime A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) hσ

theorem reversibleResistanceInversePath_sampled_measurableSpace_le (A : IntervalMedium) (x : ℝ)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (reversibleResistanceFiltration A x) (fun ω => (σ ω : WithTop ℝ≥0))) :
    hσ.measurableSpace ≤ (reversibleResistanceInversePath_sampled_isStoppingTime A x hσ).measurableSpace :=
  brownianInverseClock_sampled_measurableSpace_le A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) hσ

theorem reversibleResistancePath_borel_stopped_stronglyMeasurable (A : IntervalMedium) (x : ℝ)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (reversibleResistanceFiltration A x) (fun ω => (σ ω : WithTop ℝ≥0)))
    {f : ℝ → ℝ} (hf : Measurable f) :
    StronglyMeasurable[hσ.measurableSpace]
      (fun ω => f (reversibleResistancePath A x (σ ω) ω)) :=
  reflectedTimeChangedTrajectory_stopped_stronglyMeasurable A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) hσ (hf.comp A.resistanceInverse_continuous.measurable)

theorem reversibleResistancePath_borel_stopped_future_integrable (A : IntervalMedium) (x : ℝ)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (reversibleResistanceFiltration A x) (fun ω => (σ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    Integrable (fun ω => f (reversibleResistancePath A x (σ ω + t) ω)) brownianCompletedMeasure := by
  have hτ := finiteNNRealStoppingTime_add hσ t
  apply (integrable_const M).mono'
    (((reversibleResistancePath_borel_stopped_stronglyMeasurable A x hτ hf).mono
      hτ.measurableSpace_le).aestronglyMeasurable)
  exact Eventually.of_forall (fun ω => hb (reversibleResistancePath A x (σ ω + t) ω))

theorem reversibleResistancePath_strongMarkov (A : IntervalMedium) (x : ℝ)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (reversibleResistanceFiltration A x) (fun ω => (σ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    brownianCompletedMeasure[(fun ω => f (reversibleResistancePath A x (σ ω + t) ω)) |
      hσ.measurableSpace] =ᵐ[brownianCompletedMeasure]
        (fun ω => reversibleResistanceTransition A t f (reversibleResistancePath A x (σ ω) ω)) := by
  have he := reflectedTimeChangedTrajectory_strongMarkov A.resistanceLength A.resistanceLength_pos
    1 zero_lt_one (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) hσ t (hf.comp A.resistanceInverse_continuous.measurable)
        (fun y => hb (A.resistanceInverse y))
  refine he.trans (Eventually.of_forall (fun ω => ?_))
  exact reversibleResistanceTransition_inverse A t f
    (foldedTrajectory_mem A.resistanceLength A.resistanceLength_pos 1 (A.resistance x)
      brownianDyadicPath (reversibleResistanceInversePath A x (σ ω) ω) ω)

theorem reversibleResistancePath_strongMarkov_setIntegral (A : IntervalMedium) (x : ℝ)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (reversibleResistanceFiltration A x) (fun ω => (σ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M)
    {E : Set BrownianCompletedSample} (hE : MeasurableSet[hσ.measurableSpace] E) :
    (∫ ω in E, reversibleResistanceTransition A t f (reversibleResistancePath A x (σ ω) ω)
      ∂brownianCompletedMeasure) =
      ∫ ω in E, f (reversibleResistancePath A x (σ ω + t) ω) ∂brownianCompletedMeasure :=
  (integral_congr_ae ((reversibleResistancePath_strongMarkov A x hσ t hf hb).symm.filter_mono
    ae_restrict_le)).trans (setIntegral_condExp hσ.measurableSpace_le
      (reversibleResistancePath_borel_stopped_future_integrable A x hσ t hf hb) hE)

end TimeTraps.Probability

end
