module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeOccupationMeasure
public import TimeTraps.Probability.ReflectedAtomicHazardData
public import TimeTraps.Probability.ReflectedInteriorOccupationIdentity

@[expose] public section

/-! The fixed-level local time for the constructed physical process is
the actual reflected occupation coefficient at R(a), sampled at its own
inverse clock. Its normalization will be checked against physical occupation. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

noncomputable def reversibleResistanceLocalTime (A : IntervalMedium) (x a : ℝ)
    (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  reflectedInteriorOccupationCoefficient (A.resistance x) (Real.sqrt (2 * 1))
    A.resistanceLength (A.resistance a) (reversibleResistanceInversePath A x T ω) ω

theorem reversibleResistance_site_interior (A : IntervalMedium) {a : ℝ}
    (ha : a ∈ Ioo A.source.left A.source.right) :
    A.resistance a ∈ Ioo 0 A.resistanceLength := by
  constructor
  · simpa only [A.resistance_left] using A.resistance_strictMono
      ⟨le_rfl, A.source.increasing.le⟩ (Ioo_subset_Icc_self ha) ha.1
  · simpa only [A.resistance_right] using A.resistance_strictMono
      (Ioo_subset_Icc_self ha) ⟨A.source.increasing.le, le_rfl⟩ ha.2

theorem reversibleResistanceLocalTime_nonneg (A : IntervalMedium) (x a : ℝ)
    (T : ℝ≥0) (ω : ℕ → ℝ) : 0 ≤ reversibleResistanceLocalTime A x a T ω :=
  reflectedInteriorOccupationCoefficient_nonneg (A.resistance x)
    (Real.sqrt_pos.mpr (by norm_num)) A.resistanceLength (A.resistance a) _ ω

theorem reversibleResistanceLocalTime_jointlyMeasurable (A : IntervalMedium) (x a : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reversibleResistanceLocalTime A x a p.1 p.2) := by
  have hI : Measurable (fun p : ℝ≥0 × (ℕ → ℝ) =>
      reversibleResistanceInversePath A x p.1 p.2) :=
    reflectedPositiveTimeInversePath_jointlyMeasurable A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
        (fun y _ => A.resistanceSpeed_pos y)
  let q : ℝ≥0 × (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) :=
    fun p => (reversibleResistanceInversePath A x p.1 p.2, p.2)
  have hq : Measurable q := hI.prodMk measurable_snd
  have hm := (reflectedInteriorOccupationCoefficient_time_jointlyMeasurable
    (A.resistance x) (Real.sqrt (2 * 1)) A.resistanceLength (A.resistance a)).comp hq
  dsimp only [Function.comp_def, q] at hm
  change Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedInteriorOccupationCoefficient
    (A.resistance x) (Real.sqrt (2 * 1)) A.resistanceLength (A.resistance a)
      (reversibleResistanceInversePath A x p.1 p.2) p.2)
  exact hm

theorem reversibleResistanceInversePath_monotone (A : IntervalMedium) (x : ℝ) (ω : ℕ → ℝ) :
    Monotone (fun t => reversibleResistanceInversePath A x t ω) := by
  by_cases hω : BrownianDyadicRegular ω
  · have he := reflectedPositiveTimeInverse_eq A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) brownianDyadicPath A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
          ω hω.continuous
    have hm := (reflectedPositiveTimeSpeed A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) brownianDyadicPath A.resistanceSpeed
        A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y)
          ω hω.continuous).inverse_strictMono.monotone
    simpa only [reversibleResistanceInversePath, reflectedPositiveTimeInversePath, if_pos hω,
      ← he] using hm
  · simp only [reversibleResistanceInversePath, reflectedPositiveTimeInversePath, if_neg hω]
    exact monotone_const

end TimeTraps.Probability
