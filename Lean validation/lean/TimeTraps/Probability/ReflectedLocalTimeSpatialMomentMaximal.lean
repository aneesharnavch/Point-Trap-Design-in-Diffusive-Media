module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentIntegrand
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentEnergy
public import TimeTraps.Probability.BrownianIntegralFourthCountableMaximal
public import TimeTraps.Probability.ReflectedInteriorLocalTimeMaximal

@[expose] public section

/-! Compact-time fourth moment of the actual stochastic-integral
spatial increment, with the quantitative squared level-separation rate. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorKinkCompact_fourth_energy (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    MemLp (fun ω => ‖brownianIntegralContinuousL2 T
      (reflectedInteriorLevelIntegrand L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a -
       reflectedInteriorLevelIntegrand L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T b) ω‖)
      4 brownianDyadicMeasure ∧
    (∫ ω, ‖brownianIntegralContinuousL2 T
      (reflectedInteriorLevelIntegrand L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a -
       reflectedInteriorLevelIntegrand L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T b) ω‖ ^ 4
      ∂brownianDyadicMeasure) ≤
      600 * ∫ ω, reflectedKinkDifferenceEnergy L D x a.val b.val T ω ^ 2 ∂brownianDyadicMeasure := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have h := brownianCountableIntegral_compact_fourth_energy
    (M := ⟨2 * Real.sqrt (2 * D), by positivity⟩)
    (reflectedKinkDifference_measurable L hL a.val b.val x _)
    (reflectedKinkDifference_bound L hL a.val b.val x hσ)
    ((reflectedInteriorKinkExceptional_countable L a.val x _).union
      (reflectedInteriorKinkExceptional_countable L b.val x _))
    (reflectedKinkDifference_continuousAt L hL a.val b.val a.property b.property x hσ) T
  change MemLp (fun ω => ‖brownianIntegralContinuousL2 T
    (reflectedKinkDifferenceIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL a.val b.val a.property b.property x hσ T) ω‖) 4 brownianDyadicMeasure ∧
    (∫ ω, ‖brownianIntegralContinuousL2 T
      (reflectedKinkDifferenceIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL a.val b.val a.property b.property x hσ T) ω‖ ^ 4
      ∂brownianDyadicMeasure) ≤
      600 * ∫ ω, reflectedKinkDifferenceEnergy L D x a.val b.val T ω ^ 2 ∂brownianDyadicMeasure at h
  rw [reflectedKinkDifferenceIntegrand_eq_sub] at h
  exact h

theorem reflectedInteriorKinkCompact_fourth_spatial_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    (∫ ω, ‖brownianIntegralContinuousL2 T
      (reflectedInteriorLevelIntegrand L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a -
       reflectedInteriorLevelIntegrand L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T b) ω‖ ^ 4
      ∂brownianDyadicMeasure) ≤
      153600 * Real.sqrt (2 * D) ^ 4 * reflectedSpatialSecondConstant L D T * |a.val - b.val| ^ 2 := by
  have he := reflectedKinkDifferenceEnergy_secondMoment L hL D hD x a.val b.val T
  refine (reflectedInteriorKinkCompact_fourth_energy L hL D hD x T a b).2.trans ?_
  convert mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 600) using 1
  ring

end TimeTraps.Probability
