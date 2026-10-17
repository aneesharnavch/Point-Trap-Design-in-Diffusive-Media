module

public import TimeTraps.Probability.ReflectedRobinContactMeasure

@[expose] public section

/-! Actual endpoint coefficient measures are exactly D inverse times
the actual lower or upper regulator measure. This measure identity fixes
the Robin boundary normalization for all continuous time weights. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem reflectedRobinEndpointStieltjes_left {x L D : ℝ} {ω : ℕ → ℝ}
    (hL : 0 < L) (hD : 0 < D)
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L 0 ω)
    (hr : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω) :
    reflectedInteriorOccupationStieltjes x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 0 ω =
      Real.toNNReal (1 / D) • affineBrownianRegulatorStieltjes x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 0 ω := by
  ext r
  change _ = (Real.toNNReal (1 / D) : ℝ) * _
  rw [reflectedInteriorOccupationStieltjes_apply _ hL hω,
    affineBrownianRegulatorStieltjes_apply _ hL hr,
    reflectedRobin_endpoint_left x L hD, Real.coe_toNNReal _ (by positivity)]
  unfold affineBrownianLowerRegulator
  ring

theorem reflectedRobinEndpointStieltjes_right {x L D : ℝ} {ω : ℕ → ℝ}
    (hL : 0 < L) (hD : 0 < D)
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L L ω)
    (hr : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω) :
    reflectedInteriorOccupationStieltjes x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL L ω =
      Real.toNNReal (1 / D) • affineBrownianRegulatorStieltjes x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 1 ω := by
  ext r
  change _ = (Real.toNNReal (1 / D) : ℝ) * _
  rw [reflectedInteriorOccupationStieltjes_apply _ hL hω,
    affineBrownianRegulatorStieltjes_apply _ hL hr,
    reflectedRobin_endpoint_right x L hD, Real.coe_toNNReal _ (by positivity)]
  unfold affineBrownianUpperRegulator
  ring

theorem reflectedRobinEndpointMeasure_left {x L D : ℝ} {ω : ℕ → ℝ}
    (hL : 0 < L) (hD : 0 < D)
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L 0 ω)
    (hr : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω) :
    reflectedInteriorOccupationTimeMeasure x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 0 ω =
      Real.toNNReal (1 / D) • affineBrownianRegulatorTimeMeasure x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 0 ω := by
  rw [reflectedInteriorOccupationTimeMeasure_eq_stieltjes,
    reflectedRobinEndpointStieltjes_left hL hD hω hr, StieltjesFunction.measure_smul]
  rfl

theorem reflectedRobinEndpointMeasure_right {x L D : ℝ} {ω : ℕ → ℝ}
    (hL : 0 < L) (hD : 0 < D)
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L L ω)
    (hr : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω) :
    reflectedInteriorOccupationTimeMeasure x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL L ω =
      Real.toNNReal (1 / D) • affineBrownianRegulatorTimeMeasure x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 1 ω := by
  rw [reflectedInteriorOccupationTimeMeasure_eq_stieltjes,
    reflectedRobinEndpointStieltjes_right hL hD hω hr, StieltjesFunction.measure_smul]
  rfl

theorem reflectedRobinEndpointIntegral_left {x L D : ℝ} {ω : ℕ → ℝ}
    (hL : 0 < L) (hD : 0 < D)
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L 0 ω)
    (hr : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω)
    (w : ℝ → ℝ) (s : Set ℝ) :
    (∫ r in s, w r ∂reflectedInteriorOccupationTimeMeasure x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 0 ω) =
    (∫ r in s, w r ∂affineBrownianRegulatorTimeMeasure x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 0 ω) / D := by
  rw [reflectedRobinEndpointMeasure_left hL hD hω hr,
    Measure.restrict_smul, integral_smul_nnreal_measure]
  change (Real.toNNReal (1 / D) : ℝ) * _ = _
  rw [Real.coe_toNNReal _ (by positivity)]
  ring

theorem reflectedRobinEndpointIntegral_right {x L D : ℝ} {ω : ℕ → ℝ}
    (hL : 0 < L) (hD : 0 < D)
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L L ω)
    (hr : affineBrownianLatticeRegular x (Real.sqrt (2 * D)) L ω)
    (w : ℝ → ℝ) (s : Set ℝ) :
    (∫ r in s, w r ∂reflectedInteriorOccupationTimeMeasure x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL L ω) =
    (∫ r in s, w r ∂affineBrownianRegulatorTimeMeasure x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) hL 1 ω) / D := by
  rw [reflectedRobinEndpointMeasure_right hL hD hω hr,
    Measure.restrict_smul, integral_smul_nnreal_measure]
  change (Real.toNNReal (1 / D) : ℝ) * _ = _
  rw [Real.coe_toNNReal _ (by positivity)]
  ring

end TimeTraps.Probability

end
