module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovSampling
public import TimeTraps.Probability.BrownianBoundedOptionalSamplingAdaptation

@[expose] public section

/-! Strong Markov identities for the literal folded trajectory in the
explicit completed, right-continuous Brownian filtration. Finite
nonnegative stopping times suffice; bounded stopping times are included.
The continuous representative is removed on a single all-time event. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem foldedTrajectory_completed_observation_ae
    (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0),
      reflectedFellerExtension L hL f (foldedTrajectory L D x brownianDyadicPath t ω) =
        reflectedMarkovObservation L hL D x f t ω := by
  filter_upwards [reflectedMarkovBrownianPath_ae_all] with ω hω
  intro f t
  rw [reflectedContinuousInput_folded]
  exact congrArg (reflectedContinuousInput L hL D x f) (hω t).symm

theorem foldedTrajectory_completed_stopped_stronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ))
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    StronglyMeasurable[hτ.measurableSpace] (fun ω => reflectedFellerExtension L hL f
      (foldedTrajectory L D x brownianDyadicPath (τ ω) ω)) := by
  apply brownianCompletedStopped_stronglyMeasurable_congr hτ
    (reflectedMarkovObservation_stopped_stronglyMeasurable L hL D x f hτ)
  exact (foldedTrajectory_completed_observation_ae L hL D x).mono (fun ω hω => hω f (τ ω))

theorem foldedTrajectory_completed_stopped_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ))
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => reflectedFellerExtension L hL f
      (foldedTrajectory L D x brownianDyadicPath (τ ω) ω)) brownianCompletedMeasure :=
  (reflectedMarkovObservation_stopped_integrable L hL D x f hτ).congr
    ((foldedTrajectory_completed_observation_ae L hL D x).mono
      (fun ω hω => (hω f (τ ω)).symm))

theorem foldedTrajectory_completed_strongMarkov
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (h : ℝ≥0) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    brownianCompletedMeasure[
      (fun ω => reflectedFellerExtension L hL f
        (foldedTrajectory L D x brownianDyadicPath (τ ω + h) ω)) | hτ.measurableSpace]
      =ᵐ[brownianCompletedMeasure] (fun ω =>
        reflectedFellerExtension L hL (reflectedFellerTimeOperator L hL D h.val f)
          (foldedTrajectory L D x brownianDyadicPath (τ ω) ω)) := by
  have he := foldedTrajectory_completed_observation_ae L hL D x
  exact (condExp_congr_ae (he.mono (fun ω hω => hω f (τ ω + h)))).trans
    ((reflectedMarkovObservation_stopping_condExp L hL D hD x f h hτ).trans
      (he.mono (fun ω hω => (hω (reflectedFellerTimeOperator L hL D h.val f) (τ ω)).symm)))

theorem foldedTrajectory_completed_strongMarkov_setIntegral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (h : ℝ≥0) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, reflectedFellerExtension L hL (reflectedFellerTimeOperator L hL D h.val f)
      (foldedTrajectory L D x brownianDyadicPath (τ ω) ω) ∂brownianCompletedMeasure) =
      ∫ ω in A, reflectedFellerExtension L hL f
        (foldedTrajectory L D x brownianDyadicPath (τ ω + h) ω) ∂brownianCompletedMeasure :=
  (integral_congr_ae ((foldedTrajectory_completed_strongMarkov L hL D hD x f h hτ).symm.filter_mono
    ae_restrict_le)).trans (setIntegral_condExp hτ.measurableSpace_le
      (foldedTrajectory_completed_stopped_integrable L hL D x f (reflectedMarkovStoppingTime_add hτ h)) hA)

end TimeTraps.Probability

end
