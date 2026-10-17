module

public import TimeTraps.Probability.ReflectedPositiveTimeChangeMeasurableInverse
public import Mathlib.Probability.Process.Stopping

@[expose] public section

/-! Stopping times for the literal positive-clock inverse. The filtration
is explicitly the raw Brownian filtration augmented by all ambient
measure-null sets. This changes the ambient measurable space to its
completion. The right-continuous hull is also supported; no raw strong
adaptation or everywhere path regularity is presumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def positiveTimeChangeCompletedFiltration (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (P : Measure Ω) :
    Filtration ℝ≥0 (eventuallyMeasurableSpace mΩ (ae P)) where
  seq s := eventuallyMeasurableSpace (brownianNaturalFiltration B hBm s) (ae P)
  mono' := by
    intro s t hst A hA
    obtain ⟨C, hC, he⟩ := hA
    exact ⟨C, (brownianNaturalFiltration B hBm).mono hst C hC, he⟩
  le' := by
    intro s A hA
    obtain ⟨C, hC, he⟩ := hA
    exact ⟨C, (brownianNaturalFiltration B hBm).le s C hC, he⟩

theorem positiveTimeChangeCompletedFiltration_contains_raw
    (hBm : ∀ t, Measurable (B t)) (s : ℝ≥0) :
    brownianNaturalFiltration B hBm s ≤ positiveTimeChangeCompletedFiltration B hBm P s :=
  le_eventuallyMeasurableSpace

theorem reflectedPositiveTimeClock_completed_measurable (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (s : ℝ≥0) :
    Measurable[positiveTimeChangeCompletedFiltration B hBm P s]
      (reflectedPositiveTimeClock L D x B c s) := by
  have h := reflectedPositiveTimeClock_raw_aestronglyMeasurable hB hBm L hL D x c hc s
  exact h.stronglyMeasurable_mk.measurable.eventuallyMeasurable_of_eventuallyEq h.ae_eq_mk

theorem reflectedPositiveTimeInverse_isStoppingTime (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) :
    IsStoppingTime (positiveTimeChangeCompletedFiltration B hBm P)
      (fun ω => (reflectedPositiveTimeInverse L D x B c t ω : WithTop ℝ≥0)) := by
  intro s
  have hm := measurableSet_le (measurable_const (a := t))
    (reflectedPositiveTimeClock_completed_measurable hB hBm L hL D x c hc s)
  have he : {ω | (reflectedPositiveTimeInverse L D x B c t ω : WithTop ℝ≥0) ≤ s} =ᵐ[P]
      {ω | t ≤ reflectedPositiveTimeClock L D x B c s ω} := by
    apply eventuallyEq_set.mpr
    filter_upwards [reflectedPositiveTimeInverse_le_iff_ae hB L hL D x c hc hpos] with ω hω
    simpa only [WithTop.coe_le_coe] using hω t s
  exact EventuallyMeasurableSet.congr hm he

theorem reflectedPositiveTimeInverse_isStoppingTime_rightCont (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) :
    IsStoppingTime (positiveTimeChangeCompletedFiltration B hBm P).rightCont
      (fun ω => (reflectedPositiveTimeInverse L D x B c t ω : WithTop ℝ≥0)) := by
  intro s
  exact (positiveTimeChangeCompletedFiltration B hBm P).le_rightCont s _
    (reflectedPositiveTimeInverse_isStoppingTime hB hBm L hL D x c hc hpos t s)

end TimeTraps.Probability
