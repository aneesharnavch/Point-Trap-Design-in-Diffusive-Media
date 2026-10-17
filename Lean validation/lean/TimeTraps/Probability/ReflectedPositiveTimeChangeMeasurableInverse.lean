module

public import TimeTraps.Probability.ReflectedPositiveTimeChangeMeasurable

@[expose] public section

/-! The literal inverse is characterized by clock-level events on each
continuous path. The actual Brownian continuity event therefore gives
AE measurability of every fixed-time inverse, without altering its values. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedPositiveTimeInverse_le_iff (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (ω : Ω) (hω : Continuous (fun s => B s ω)) (t s : ℝ≥0) :
    reflectedPositiveTimeInverse L D x B c t ω ≤ s ↔ t ≤ reflectedPositiveTimeClock L D x B c s ω := by
  let v := reflectedPositiveTimeSpeed L hL D x B c hc hpos ω hω
  rw [congrFun (reflectedPositiveTimeInverse_eq L hL D x B c hc hpos ω hω) t,
    congrFun (reflectedPositiveTimeClock_eq L hL D x B c hc hpos ω hω) s]
  change v.inverse t ≤ s ↔ t ≤ v.clock s
  constructor
  · intro h
    simpa only [v.clock_inverse] using v.clock_strictMono.monotone h
  · intro h
    apply v.clock_strictMono.le_iff_le.mp
    simpa only [v.clock_inverse] using h

theorem reflectedPositiveTimeInverse_le_iff_ae (hB : IsBrownianReal B P)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    ∀ᵐ ω ∂P, ∀ t s : ℝ≥0,
      reflectedPositiveTimeInverse L D x B c t ω ≤ s ↔
        t ≤ reflectedPositiveTimeClock L D x B c s ω := by
  filter_upwards [hB.cont] with ω hω
  exact fun t s => reflectedPositiveTimeInverse_le_iff L hL D x c hc hpos ω hω t s

theorem reflectedPositiveTimeInverse_aemeasurable (hB : IsBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L))
    (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (t : ℝ≥0) :
    AEMeasurable (reflectedPositiveTimeInverse L D x B c t) P := by
  have hn : NullMeasurable (reflectedPositiveTimeInverse L D x B c t) P := by
    change @Measurable (NullMeasurableSpace Ω P) ℝ≥0 _ _ _
    apply measurable_of_Iic
    intro s
    have he : {ω | reflectedPositiveTimeInverse L D x B c t ω ≤ s} =ᵐ[P]
        {ω | t ≤ reflectedPositiveTimeClock L D x B c s ω} := by
      apply eventuallyEq_set.mpr
      filter_upwards [reflectedPositiveTimeInverse_le_iff_ae hB L hL D x c hc hpos] with ω hω
      exact hω t s
    exact (measurableSet_le measurable_const
      (reflectedPositiveTimeClock_measurable hjoint L hL D x c hc s)).nullMeasurableSet.congr he.symm
  exact hn.aemeasurable

end TimeTraps.Probability
