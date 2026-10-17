module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeOccupation
public import TimeTraps.Analysis.DensityMapIntervals

@[expose] public section

/-! The transported physical density is identified with the literal
occupation measure of the constructed path. Its total mass is physical
time, on one event simultaneously for all horizons. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

theorem reversibleResistanceOccupationDensity_integrable_mass (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      Integrable (reversibleResistanceOccupationDensity A x T ω) volume ∧
        (∫ z, reversibleResistanceOccupationDensity A x T ω z) = T.val := by
  filter_upwards [reversibleResistanceOccupationDensity_bounded_occupation A x] with ω hω
  intro T
  have hi := hω (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num) T
  simpa only [one_mul, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one] using
    And.intro hi.1 hi.2.2

theorem reversibleResistanceOccupationDensity_measure (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      volume.withDensity (fun z => ENNReal.ofReal (reversibleResistanceOccupationDensity A x T ω z)) =
        brownianOccupationMeasure (reversibleResistancePath A x) T ω := by
  filter_upwards [reversibleResistanceOccupationDensity_bounded_occupation A x] with ω hω
  intro T
  apply Measure.ext
  intro s hs
  have hb (z : ℝ) : |s.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    by_cases hz : z ∈ s
    · rw [indicator_of_mem hz, abs_one]
    · rw [indicator_of_notMem hz, abs_zero]
      exact zero_le_one
  have hi := hω (s.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hs) 1 hb T
  rw [withDensity_ofReal_apply_indicator
    (fun z => reversibleResistanceOccupationDensity_nonneg A x T ω z) hs hi.1]
  have hm := finite_map_apply_ofReal_indicator
    (ν := volume.restrict (Ioc (0 : ℝ) T.val))
    (brownianOccupationMeasure_path_measurable (reversibleResistancePath_jointlyMeasurable A x) ω) hs
  change _ = (volume.restrict (Ioc (0 : ℝ) T.val)).map
    (fun t => reversibleResistancePath A x t.toNNReal ω) s
  rw [hm, hi.2.2]
  exact congrArg ENNReal.ofReal (intervalIntegral.integral_of_le T.coe_nonneg)

end TimeTraps.Probability
