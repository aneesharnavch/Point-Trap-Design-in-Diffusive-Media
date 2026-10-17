module

public import TimeTraps.Probability.BrownianLocalTimeGridMeasure
public import TimeTraps.Probability.BrownianLocalTimeTimeMeasure
public import TimeTraps.Analysis.OccupationDensityAllTimes

@[expose] public section

/-! One full-probability event gives the actual occupation density measure
at every nonnegative horizon. The extension uses ordered countable grid
values and monotone convergence, not an uncountable intersection of
fixed-time events or spatial sample continuity. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem brownianLocalTimeTimeMeasure_eq_of_grid {ω : ℕ → ℝ}
    (horder : ∀ᵐ a ∂(volume : Measure ℝ), brownianLocalTimeGridOrdered a ω)
    (hocc : ∀ i : ℕ, volume.withDensity (fun a => ENNReal.ofReal
      (brownianDyadicLocalTimeJointVersion a (brownianDyadicTime i) ω)) =
        brownianOccupationMeasure brownianDyadicPath (brownianDyadicTime i) ω)
    (T : ℝ≥0) :
    brownianLocalTimeTimeMeasure T ω = brownianOccupationMeasure brownianDyadicPath T ω := by
  obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
  have hNT : T ≤ (N : ℝ≥0) := hN
  let k : ℕ → ℕ := fun n => Nat.pair n (brownianDyadicFloor T n)
  have hf (i : ℕ) : Measurable
      (fun a => brownianDyadicLocalTimeJointVersion a (brownianDyadicTime i) ω) :=
    Measurable.of_uncurry_right
      (f := fun a ω => brownianDyadicLocalTimeJointVersion a (brownianDyadicTime i) ω)
      (y := ω) (brownianDyadicLocalTimeJointVersion_timeSlice_measurable (brownianDyadicTime i))
  have he := occupationDensity_grid_eq_occupation (μ := (volume : Measure ℝ))
    brownianDyadicTime (fun i a => brownianDyadicLocalTimeJointVersion a (brownianDyadicTime i) ω)
    (brownianOccupationMeasure_path_measurable brownianDyadicPath_jointly_measurable ω)
    hf horder T k (brownianLocalTimeSampleTime_monotone T)
    (fun n => brownianLocalTimeSampleTime_le n T) (brownianLocalTimeSampleTime_tendsto T)
    ⟨Nat.pair 0 N, fun n => brownianLocalTimeSampleTime_le_integer hNT n⟩ hocc
  change brownianLocalTimeTimeMeasure T ω = brownianOccupationMeasure brownianDyadicPath T ω at he
  exact he

theorem brownianLocalTimeTimeMeasure_all_times_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      brownianLocalTimeTimeMeasure T ω = brownianOccupationMeasure brownianDyadicPath T ω := by
  filter_upwards [brownianLocalTimeGridOrdered_spatial_ae, brownianLocalTimeGridOccupation_ae]
    with ω horder hocc
  exact brownianLocalTimeTimeMeasure_eq_of_grid horder hocc

theorem brownianLocalTimeTimeMeasureRegular_all_times_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0, brownianLocalTimeTimeMeasureRegular T ω := by
  filter_upwards [brownianLocalTimeTimeMeasure_all_times_ae] with ω he
  intro T p q
  rw [he T]

theorem brownianLocalTimeTimeField_all_times_mass_ae :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      Integrable (fun a => brownianLocalTimeTimeField a T ω) volume ∧
        (∫ a, brownianLocalTimeTimeField a T ω) = T.val := by
  filter_upwards [brownianLocalTimeTimeMeasureRegular_all_times_ae] with ω hω
  intro T
  exact ⟨brownianLocalTimeTimeMeasureRegular_integrable (hω T),
    brownianLocalTimeTimeMeasureRegular_integral (hω T)⟩

end TimeTraps.Probability
