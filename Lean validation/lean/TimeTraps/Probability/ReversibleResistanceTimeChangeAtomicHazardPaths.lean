module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeAtomicHazard

@[expose] public section

/-! All-time paths of the physical hazard and exact clock transport.
The finite family may contain repeated sites and may be empty. The
occupation interpretation of each actual trap uses the interior-level
contact theorem separately. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

variable {ι : Type*} [Fintype ι]

theorem reversibleResistanceAtomicHazard_paths (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => reversibleResistanceAtomicHazard A x a κ t ω) ∧
        Monotone (fun t => reversibleResistanceAtomicHazard A x a κ t ω) ∧
          reversibleResistanceAtomicHazard A x a κ 0 ω = 0 ∧
      Continuous (fun t => reversibleResistanceAtomicSurvival A x a κ t ω) ∧
        Antitone (fun t => reversibleResistanceAtomicSurvival A x a κ t ω) ∧
          reversibleResistanceAtomicSurvival A x a κ 0 ω = 1 := by
  filter_upwards [reflectedAtomicHazard_paths_ae A.resistanceLength A.resistanceLength_pos
    1 zero_lt_one (A.resistance x) (fun i => A.resistance (a i)) κ hκ] with ω hω
  have hI : Continuous (fun t => reversibleResistanceInversePath A x t ω) :=
    reflectedPositiveTimeInversePath_continuous A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
        (fun y _ => A.resistanceSpeed_pos y) ω
  refine ⟨hω.1.comp hI, hω.2.1.comp (reversibleResistanceInversePath_monotone A x ω), ?_,
    hω.2.2.2.1.comp hI, hω.2.2.2.2.1.comp_monotone
      (reversibleResistanceInversePath_monotone A x ω), ?_⟩
  · rw [reversibleResistanceAtomicHazard_reference, reversibleResistanceInversePath_zero]
    exact hω.2.2.1
  · rw [reversibleResistanceAtomicSurvival_reference, reversibleResistanceInversePath_zero]
    exact hω.2.2.2.2.2

theorem reversibleResistanceAtomicHazard_clock (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s : ℝ≥0) :
    reversibleResistanceAtomicHazard A x a κ (reversibleResistanceClock A x s ω) ω =
      reflectedAtomicHazard A.resistanceLength 1 (A.resistance x)
        (fun i => A.resistance (a i)) κ s ω := by
  rw [reversibleResistanceAtomicHazard_reference, reversibleResistanceInversePath_clock A x hω s]

theorem reversibleResistanceAtomicSurvival_clock (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (s : ℝ≥0) :
    reversibleResistanceAtomicSurvival A x a κ (reversibleResistanceClock A x s ω) ω =
      reflectedAtomicSurvival A.resistanceLength 1 (A.resistance x)
        (fun i => A.resistance (a i)) κ s ω := by
  rw [reversibleResistanceAtomicSurvival_reference, reversibleResistanceInversePath_clock A x hω s]

theorem reversibleResistanceAtomicHazard_literal_reference (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      reversibleResistanceAtomicHazard A x a κ T ω =
        reflectedAtomicHazard A.resistanceLength 1 (A.resistance x)
          (fun i => A.resistance (a i)) κ (reversibleResistanceInverseClock A x T ω) ω := by
  filter_upwards [reflectedPositiveTimeInversePath_eq_ae A.resistanceLength 1
    (A.resistance x) A.resistanceSpeed] with ω hω
  intro T
  rw [reversibleResistanceAtomicHazard_reference]
  exact congrArg (fun t => reflectedAtomicHazard A.resistanceLength 1 (A.resistance x)
    (fun i => A.resistance (a i)) κ t ω) (hω T)

end TimeTraps.Probability
