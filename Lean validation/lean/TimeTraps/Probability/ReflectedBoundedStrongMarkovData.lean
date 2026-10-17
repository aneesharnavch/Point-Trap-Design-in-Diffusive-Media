module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingApproximation
public import TimeTraps.Probability.ReflectedContinuousDynkinData

@[expose] public section

/-! A continuous representative of the actual reflected observations in
the completed, right-continuous Brownian filtration. The representative
agrees with the original path at every time on one proved full-measure
event. Bounds come from the compact spatial test, not a stopping premise. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

def reflectedMarkovBrownianPath (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ := by
  classical
  exact if BrownianDyadicRegular ω then brownianDyadicPath t ω else 0

theorem reflectedMarkovBrownianPath_continuous (ω : BrownianCompletedSample) :
    Continuous (fun t => reflectedMarkovBrownianPath t ω) := by
  by_cases hω : BrownianDyadicRegular ω
  · simpa only [reflectedMarkovBrownianPath, if_pos hω] using hω.continuous
  · simp only [reflectedMarkovBrownianPath, if_neg hω]
    exact continuous_const

theorem reflectedMarkovBrownianPath_ae_all :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t,
      reflectedMarkovBrownianPath t ω = brownianDyadicPath t ω := by
  have h : ∀ᵐ ω ∂brownianCompletedMeasure, BrownianDyadicRegular ω := brownianDyadic_regular_ae
  exact h.mono (fun ω hω t => if_pos hω)

theorem reflectedMarkovBrownianPath_stronglyAdapted :
    StronglyAdapted brownianCompletedFiltration reflectedMarkovBrownianPath := by
  intro t
  have he : (fun ω : ℕ → ℝ => reflectedMarkovBrownianPath t ω) =ᵐ[brownianDyadicMeasure]
      brownianDyadicPath t := brownianDyadic_regular_ae.mono (fun ω hω => if_pos hω)
  exact ((brownianFiltration_stronglyAdapted t).measurable.eventuallyMeasurable_of_eventuallyEq
    he).stronglyMeasurable

def reflectedMarkovObservation (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  reflectedContinuousInput L hL D x f (reflectedMarkovBrownianPath t ω)

theorem reflectedMarkovObservation_continuous (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (ω : BrownianCompletedSample) :
    Continuous (fun t => reflectedMarkovObservation L hL D x f t ω) :=
  (reflectedContinuousInput_continuous L hL D x f).comp
    (reflectedMarkovBrownianPath_continuous ω)

theorem reflectedMarkovObservation_bound (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) (ω : BrownianCompletedSample) :
    ‖reflectedMarkovObservation L hL D x f t ω‖ ≤ ‖f‖ :=
  reflectedContinuousInput_bound L hL D x f _

theorem reflectedMarkovObservation_stronglyAdapted (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    StronglyAdapted brownianCompletedFiltration.rightCont
      (reflectedMarkovObservation L hL D x f) := by
  intro t
  exact ((reflectedContinuousInput_continuous L hL D x f).comp_stronglyMeasurable
    (reflectedMarkovBrownianPath_stronglyAdapted t)).mono
      (brownianCompletedFiltration.le_rightCont t)

theorem reflectedMarkovObservation_stopped_stronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ))
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    StronglyMeasurable[hτ.measurableSpace]
      (fun ω => reflectedMarkovObservation L hL D x f (τ ω) ω) := by
  exact (measurable_stoppedValue
    ((reflectedMarkovObservation_stronglyAdapted L hL D x f).isStronglyProgressive_of_continuous
      (reflectedMarkovObservation_continuous L hL D x f)) hτ).stronglyMeasurable

theorem reflectedMarkovObservation_stopped_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ))
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => reflectedMarkovObservation L hL D x f (τ ω) ω)
      brownianCompletedMeasure := by
  apply (integrable_const ‖f‖).mono'
    ((reflectedMarkovObservation_stopped_stronglyMeasurable L hL D x f hτ).mono
      hτ.measurableSpace_le).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => reflectedMarkovObservation_bound L hL D x f _ ω)

theorem reflectedMarkovStoppingTime_add {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0) :
    IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω + h : ℝ≥0)) := by
  intro s
  by_cases hs : h ≤ s
  · have he : {ω | (τ ω + h : WithTop ℝ≥0) ≤ s} =
        {ω | (τ ω : WithTop ℝ≥0) ≤ (s - h : ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, ← WithTop.coe_add, WithTop.coe_le_coe]
      exact (le_tsub_iff_right hs).symm
    change MeasurableSet[brownianCompletedFiltration.rightCont s]
      {ω | (τ ω + h : WithTop ℝ≥0) ≤ s}
    rw [he]
    exact (brownianCompletedFiltration.rightCont.mono tsub_le_self) _ (hτ (s - h))
  · have he : {ω | ((τ ω + h : ℝ≥0) : WithTop ℝ≥0) ≤ s} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_empty_iff_false, iff_false]
      exact fun hh => hs ((le_add_of_nonneg_left bot_le).trans hh)
    rw [he]
    exact @MeasurableSet.empty _ (brownianCompletedFiltration.rightCont s)

end TimeTraps.Probability

end
