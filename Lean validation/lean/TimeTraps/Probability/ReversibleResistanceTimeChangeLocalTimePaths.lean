module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeData

@[expose] public section

/-! The transported fixed-level coefficient has continuous increasing
paths and starts at zero. Its physical occupation-density normalization
is proved at every interior level simultaneously in time; no uncountable
intersection of level events is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

theorem reversibleResistanceLocalTime_paths (A : IntervalMedium) (x a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => reversibleResistanceLocalTime A x a t ω) ∧
        Monotone (fun t => reversibleResistanceLocalTime A x a t ω) ∧
          reversibleResistanceLocalTime A x a 0 ω = 0 := by
  filter_upwards [reflectedInteriorLocalTimeRegular_ae (A.resistance x)
    (Real.sqrt (2 * 1)) A.resistanceLength (A.resistance a)] with ω hω
  have hσ : 0 < Real.sqrt (2 * (1 : ℝ)) := Real.sqrt_pos.mpr (by norm_num)
  have hI : Continuous (fun t => reversibleResistanceInversePath A x t ω) :=
    reflectedPositiveTimeInversePath_continuous A.resistanceLength A.resistanceLength_pos
      1 (A.resistance x) A.resistanceSpeed A.resistanceSpeed_continuous.continuousOn
        (fun y _ => A.resistanceSpeed_pos y) ω
  refine ⟨?_, ?_, ?_⟩
  · exact ((reflectedInteriorCorrection_continuous hσ A.resistanceLength_pos hω).div_const
      ((Real.sqrt (2 * 1)) ^ 2)).comp hI
  · intro s t hst
    exact div_le_div_of_nonneg_right
      (reflectedInteriorCorrection_monotone hσ A.resistanceLength_pos hω
        (reversibleResistanceInversePath_monotone A x ω hst)) (sq_nonneg _)
  · rw [reversibleResistanceLocalTime, reversibleResistanceInversePath_zero,
      reflectedInteriorOccupationCoefficient, reflectedInteriorCorrection_zero hσ hω, zero_div]

theorem reversibleResistanceLocalTime_density_normalization (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      reversibleResistanceOccupationDensity A x T ω a =
        A.source.density a * reversibleResistanceLocalTime A x a T ω := by
  filter_upwards [reflectedInteriorOccupationCoefficient_density_all_times_ae
    A.resistanceLength A.resistanceLength_pos 1 zero_lt_one (A.resistance x)
      (A.resistance a) (reversibleResistance_site_interior A ha)] with ω hω
  intro T
  rw [reversibleResistanceOccupationDensity, indicator_of_mem ha]
  exact congrArg (fun q => A.source.density a * q)
    (hω (reversibleResistanceInversePath A x T ω)).symm

end TimeTraps.Probability
