module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovTimeChange
public import TimeTraps.Probability.BrownianBoundedOptionalSamplingResistance

@[expose] public section

/-! The literal resistance-time-changed diffusion satisfies the Markov
conditional identity in its explicit stopped Brownian filtration. The
transition is the actual expectation, with original conductance and speed
density unchanged; equality with the original uncompleted integral is proved. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

def reversibleResistanceTransition (A : IntervalMedium) (t : ℝ≥0) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ ω : BrownianCompletedSample, f (reversibleResistancePath A x t ω) ∂brownianCompletedMeasure

theorem reversibleResistanceTransition_original (A : IntervalMedium) (t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) (x : ℝ) :
    reversibleResistanceTransition A t f x =
      ∫ ω, f (reversibleResistancePath A x t ω) ∂brownianDyadicMeasure :=
  completedMeasure_integral brownianDyadicMeasure
    (hf.comp ((reversibleResistancePath_jointlyMeasurable A x).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable

theorem reversibleResistanceTransition_reference (A : IntervalMedium) (t : ℝ≥0)
    (f : ℝ → ℝ) (x : ℝ) :
    reversibleResistanceTransition A t f x =
      reflectedTimeChangedOperator A.resistanceLength 1 A.resistanceSpeed t
        (fun y => f (A.resistanceInverse y)) (A.resistance x) := rfl

theorem reversibleResistanceTransition_inverse (A : IntervalMedium) (t : ℝ≥0)
    (f : ℝ → ℝ) {y : ℝ} (hy : y ∈ Icc 0 A.resistanceLength) :
    reflectedTimeChangedOperator A.resistanceLength 1 A.resistanceSpeed t
      (fun y => f (A.resistanceInverse y)) y =
        reversibleResistanceTransition A t f (A.resistanceInverse y) := by
  rw [reversibleResistanceTransition_reference, A.resistance_inverse hy]

theorem reversibleResistancePath_borel_stronglyMeasurable (A : IntervalMedium) (x : ℝ) (t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) :
    StronglyMeasurable[reversibleResistanceFiltration A x t]
      (fun ω : BrownianCompletedSample => f (reversibleResistancePath A x t ω)) :=
  reflectedTimeChangedTrajectory_stronglyMeasurable A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) t (hf.comp A.resistanceInverse_continuous.measurable)

theorem reversibleResistancePath_borel_integrable (A : IntervalMedium) (x : ℝ) (t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    Integrable (fun ω : BrownianCompletedSample => f (reversibleResistancePath A x t ω))
      brownianCompletedMeasure := by
  apply (integrable_const M).mono'
    (((reversibleResistancePath_borel_stronglyMeasurable A x t hf).mono
      ((reversibleResistanceFiltration A x).le t)).aestronglyMeasurable)
  exact Eventually.of_forall (fun ω => hb (reversibleResistancePath A x t ω))

theorem reversibleResistanceTransition_bound (A : IntervalMedium) (t : ℝ≥0)
    {f : ℝ → ℝ} {M : ℝ} (hb : ∀ y, |f y| ≤ M) (x : ℝ) :
    |reversibleResistanceTransition A t f x| ≤ M :=
  reflectedTimeChangedOperator_bound A.resistanceLength 1 A.resistanceSpeed t
    (fun y => hb (A.resistanceInverse y)) (A.resistance x)

theorem reversibleResistancePath_markov (A : IntervalMedium) (x : ℝ) (s t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    brownianCompletedMeasure[(fun ω => f (reversibleResistancePath A x (s + t) ω)) |
      reversibleResistanceFiltration A x s] =ᵐ[brownianCompletedMeasure]
        (fun ω => reversibleResistanceTransition A t f (reversibleResistancePath A x s ω)) := by
  have he := reflectedTimeChangedTrajectory_markov A.resistanceLength A.resistanceLength_pos
    1 zero_lt_one (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
      (fun y _ => A.resistanceSpeed_pos y) s t (hf.comp A.resistanceInverse_continuous.measurable)
        (fun y => hb (A.resistanceInverse y))
  refine he.trans (Eventually.of_forall (fun ω => ?_))
  exact reversibleResistanceTransition_inverse A t f
    (foldedTrajectory_mem A.resistanceLength A.resistanceLength_pos 1 (A.resistance x)
      brownianDyadicPath (reversibleResistanceInversePath A x s ω) ω)

theorem reversibleResistancePath_markov_setIntegral (A : IntervalMedium) (x : ℝ) (s t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M)
    {E : Set BrownianCompletedSample} (hE : MeasurableSet[reversibleResistanceFiltration A x s] E) :
    (∫ ω in E, reversibleResistanceTransition A t f (reversibleResistancePath A x s ω)
      ∂brownianCompletedMeasure) =
      ∫ ω in E, f (reversibleResistancePath A x (s + t) ω) ∂brownianCompletedMeasure :=
  (integral_congr_ae ((reversibleResistancePath_markov A x s t hf hb).symm.filter_mono
    ae_restrict_le)).trans (setIntegral_condExp ((reversibleResistanceFiltration A x).le s)
      (reversibleResistancePath_borel_integrable A x (s + t) hf hb) hE)

end TimeTraps.Probability

end
