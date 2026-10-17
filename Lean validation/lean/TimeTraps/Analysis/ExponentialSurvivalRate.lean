module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-! Positive two-sided exponential bounds determine the logarithmic
survival rate. No spectral remainder or differentiability of survival
is asserted by this elementary limit theorem. -/

namespace TimeTraps.Analysis

open Filter
open scoped NNReal Topology

theorem exponentialSurvivalRate {w : ℝ≥0 → ℝ} {c C ev : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ T : ℝ≥0, c * Real.exp (-ev * T.val) ≤ w T ∧
      w T ≤ C * Real.exp (-ev * T.val)) :
    Tendsto (fun T : ℝ≥0 => -Real.log (w T) / T.val) atTop (𝓝 ev) := by
  have ht : Tendsto (fun T : ℝ≥0 => T.val) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hl : Tendsto (fun T : ℝ≥0 => ev - Real.log C / T.val) atTop (𝓝 ev) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (ht.const_div_atTop (Real.log C))
  have hr : Tendsto (fun T : ℝ≥0 => ev - Real.log c / T.val) atTop (𝓝 ev) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (ht.const_div_atTop (Real.log c))
  have hbound : ∀ᶠ T : ℝ≥0 in atTop,
      ev - Real.log C / T.val ≤ -Real.log (w T) / T.val ∧
      -Real.log (w T) / T.val ≤ ev - Real.log c / T.val := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with T hT
    have hpos : 0 < T.val := hT
    have hw : 0 < w T := (mul_pos hc (Real.exp_pos _)).trans_le (hb T).1
    have ha := Real.log_le_log (mul_pos hc (Real.exp_pos _)) (hb T).1
    have hz := Real.log_le_log hw (hb T).2
    rw [Real.log_mul hc.ne' (Real.exp_ne_zero _), Real.log_exp] at ha
    rw [Real.log_mul hC.ne' (Real.exp_ne_zero _), Real.log_exp] at hz
    constructor
    · apply (le_div_iff₀ hpos).mpr
      rw [sub_mul, div_mul_cancel₀ _ hpos.ne']
      nlinarith
    · apply (div_le_iff₀ hpos).mpr
      rw [sub_mul, div_mul_cancel₀ _ hpos.ne']
      nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr
    (hbound.mono (fun _ h => h.1)) (hbound.mono (fun _ h => h.2))

end TimeTraps.Analysis
