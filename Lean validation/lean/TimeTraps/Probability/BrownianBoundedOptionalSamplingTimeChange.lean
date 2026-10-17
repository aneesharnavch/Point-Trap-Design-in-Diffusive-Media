module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingConsequences
public import TimeTraps.Probability.ReflectedPositiveTimeChangeMeasurablePath

@[expose] public section

/-! Application of bounded optional sampling to the proved inverse-clock
version. The original inverse has the same integrable, zero-mean stopped
integral by its all-time almost-sure agreement with that version. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianCompletedInversePath_isStoppingTime (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω : BrownianCompletedSample => (reflectedPositiveTimeInversePath L D x c t ω : WithTop ℝ≥0)) := by
  intro s
  exact brownianCompletedFiltration.le_rightCont s _
    (reflectedPositiveTimeInversePath_isStoppingTime L hL D x c hc hpos t s)

theorem brownianCompletedIntegralPath_inverse_optionalSampling (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y) (t : ℝ≥0) :
    brownianCompletedMeasure[brownianCompletedIntegralPath f (t / m) |
      (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t).measurableSpace]
      =ᵐ[brownianCompletedMeasure] (fun ω =>
        brownianCompletedIntegralPath f (reflectedPositiveTimeInversePath L D x c t ω) ω) :=
  brownianCompletedIntegralPath_optionalSampling f
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t)
    (reflectedPositiveTimeInversePath_bound L hL D x c hc hpos m hm hmc t)

theorem brownianCompletedIntegralPath_inverse_integrable_mean (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y) (t : ℝ≥0) :
    Integrable (fun ω => brownianCompletedIntegralPath f
      (reflectedPositiveTimeInversePath L D x c t ω) ω) brownianCompletedMeasure ∧
      (∫ ω, brownianCompletedIntegralPath f (reflectedPositiveTimeInversePath L D x c t ω) ω
        ∂brownianCompletedMeasure) = 0 :=
  ⟨brownianCompletedIntegralPath_stopped_integrable f
      (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t)
      (reflectedPositiveTimeInversePath_bound L hL D x c hc hpos m hm hmc t),
    brownianCompletedIntegralPath_stopped_mean f
      (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t)
      (reflectedPositiveTimeInversePath_bound L hL D x c hc hpos m hm hmc t)⟩

theorem brownianCompletedIntegralPath_literalInverse_integrable_mean (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y) (t : ℝ≥0) :
    Integrable (fun ω => brownianCompletedIntegralPath f
      (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω) brownianCompletedMeasure ∧
      (∫ ω, brownianCompletedIntegralPath f
        (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω ∂brownianCompletedMeasure) = 0 := by
  have he : (fun ω => brownianCompletedIntegralPath f
      (reflectedPositiveTimeInversePath L D x c t ω) ω) =ᵐ[brownianCompletedMeasure]
      (fun ω => brownianCompletedIntegralPath f
        (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω) := by
    filter_upwards [reflectedPositiveTimeInversePath_eq_ae L D x c] with ω hω
    rw [hω t]
  obtain ⟨hi, hmz⟩ := brownianCompletedIntegralPath_inverse_integrable_mean f L hL D x c hc hpos m hm hmc t
  exact ⟨hi.congr he, (integral_congr_ae he).symm.trans hmz⟩

theorem brownianIntegralGlobalPath_literalInverse_integrable_mean (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y) (t : ℝ≥0) :
    Integrable (fun ω => brownianIntegralGlobalPath f
      (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω) brownianDyadicMeasure ∧
      (∫ ω, brownianIntegralGlobalPath f
        (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω ∂brownianDyadicMeasure) = 0 := by
  have hi := reflectedPositiveTimeInverse_aemeasurable brownianDyadicPath_isBrownianReal
    brownianDyadicPath_jointly_measurable L hL D x c hc hpos t
  have he : AEMeasurable (fun ω => brownianIntegralGlobalPath f
      (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω) brownianDyadicMeasure :=
    (brownianIntegralGlobalPath_jointlyMeasurable f).comp_aemeasurable (hi.prodMk aemeasurable_id)
  obtain ⟨hcomp, hzero⟩ := brownianCompletedIntegralPath_literalInverse_integrable_mean
    f L hL D x c hc hpos m hm hmc t
  refine ⟨((completedMeasure_identity_preserving brownianDyadicMeasure).integrable_comp
    he.aestronglyMeasurable).mp hcomp, ?_⟩
  exact (completedMeasure_integral brownianDyadicMeasure he.aestronglyMeasurable).symm.trans hzero

end TimeTraps.Probability
