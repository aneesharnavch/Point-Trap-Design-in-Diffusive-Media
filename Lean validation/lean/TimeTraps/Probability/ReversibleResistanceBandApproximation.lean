module

public import TimeTraps.Probability.ReversibleResistanceSpeedContinuous
public import TimeTraps.Probability.BrownianLocalTimeBandData
public import Mathlib.Topology.MetricSpace.ThickenedIndicator

@[expose] public section

/-! Uniformly bounded continuous approximations of the literal open
occupation band, with pointwise convergence at every spatial point. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal Topology BoundedContinuousFunction

def resistanceOpenApproximation (U : Set ℝ) (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => 1 - (thickenedIndicator
      (by positivity : 0 < 1 / ((n : ℝ) + 1)) Uᶜ x : ℝ),
      continuous_const.sub (NNReal.continuous_coe.comp
        (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) Uᶜ).continuous)⟩ 2 (by
      intro x y
      change dist (1 - (thickenedIndicator _ Uᶜ x : ℝ))
        (1 - (thickenedIndicator _ Uᶜ y : ℝ)) ≤ 2
      have hx : (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) Uᶜ x : ℝ) ≤ 1 :=
        NNReal.coe_le_coe.mpr (thickenedIndicator_le_one _ _ _)
      have hy : (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) Uᶜ y : ℝ) ≤ 1 :=
        NNReal.coe_le_coe.mpr (thickenedIndicator_le_one _ _ _)
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [NNReal.coe_nonneg (thickenedIndicator
        (by positivity : 0 < 1 / ((n : ℝ) + 1)) Uᶜ x),
        NNReal.coe_nonneg (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) Uᶜ y)])

theorem resistanceOpenApproximation_bounds (U : Set ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ resistanceOpenApproximation U n x ∧ resistanceOpenApproximation U n x ≤ 1 := by
  change 0 ≤ 1 - (thickenedIndicator _ Uᶜ x : ℝ) ∧
    1 - (thickenedIndicator _ Uᶜ x : ℝ) ≤ 1
  have hx : (thickenedIndicator (by positivity : 0 < 1 / ((n : ℝ) + 1)) Uᶜ x : ℝ) ≤ 1 :=
    NNReal.coe_le_coe.mpr (thickenedIndicator_le_one _ _ _)
  constructor <;> linarith [NNReal.coe_nonneg (thickenedIndicator
    (by positivity : 0 < 1 / ((n : ℝ) + 1)) Uᶜ x)]

theorem resistanceOpenApproximation_norm_le (U : Set ℝ) (n : ℕ) (x : ℝ) :
    ‖resistanceOpenApproximation U n x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (resistanceOpenApproximation_bounds U n x).1]
  exact (resistanceOpenApproximation_bounds U n x).2

theorem resistanceOpenApproximation_tendsto {U : Set ℝ} (hU : IsOpen U) (x : ℝ) :
    Tendsto (fun n => resistanceOpenApproximation U n x) atTop
      (𝓝 (U.indicator (fun _ => (1 : ℝ)) x)) := by
  have h := thickenedIndicator_tendsto_indicator_closure
    (fun n : ℕ => by positivity : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat Uᶜ
  have hx := (tendsto_pi_nhds.mp h) x
  have hr := (tendsto_const_nhds (x := (1 : ℝ))).sub (NNReal.continuous_coe.continuousAt.tendsto.comp hx)
  change Tendsto (fun n => 1 - (thickenedIndicator _ Uᶜ x : ℝ)) atTop _
  have he : 1 - NNReal.toReal ((closure Uᶜ).indicator (fun _ => (1 : ℝ≥0)) x) =
      U.indicator (fun _ => (1 : ℝ)) x := by
    rw [hU.isClosed_compl.closure_eq]
    by_cases hxU : x ∈ U <;> simp [hxU]
  rw [he] at hr
  exact hr

theorem resistanceBandApproximation_tendsto (a h x : ℝ) :
    Tendsto (fun n => resistanceOpenApproximation (Ioo (a - h) (a + h)) n x)
      atTop (𝓝 (brownianBandIndicator a h x)) :=
  resistanceOpenApproximation_tendsto isOpen_Ioo x

end TimeTraps.Probability

end
