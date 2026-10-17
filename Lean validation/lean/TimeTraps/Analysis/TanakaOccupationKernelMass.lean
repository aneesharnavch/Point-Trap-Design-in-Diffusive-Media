module

public import TimeTraps.Analysis.TanakaOccupationKernel

@[expose] public section

/-! The smooth occupation kernel has total mass exactly one. This is
an improper-integral consequence of its actual primitive and limits. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter
open scoped Topology

theorem tanakaSmoothAbs_positive_ratio (ε : ℝ) {x : ℝ} (hx : 0 < x) :
    x / tanakaSmoothAbs ε x = 1 / Real.sqrt (1 + (ε / x) ^ 2) := by
  have hn := ne_of_gt hx
  have hr : x ^ 2 + ε ^ 2 = x ^ 2 * (1 + (ε / x) ^ 2) := by
    field_simp
  have hs : Real.sqrt (1 + (ε / x) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [tanakaSmoothAbs, hr, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx.le]
  field_simp

theorem tanakaSmoothAbs_deriv_neg {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (tanakaSmoothAbs ε) (-x) = -deriv (tanakaSmoothAbs ε) x := by
  rw [tanakaSmoothAbs_deriv hε, tanakaSmoothAbs_deriv hε]
  simp only [tanakaSmoothAbs, neg_sq, neg_div]

theorem tanakaSmoothAbs_deriv_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (deriv (tanakaSmoothAbs ε)) atTop (𝓝 1) := by
  have hq : Tendsto (fun x : ℝ => ε / x) atTop (𝓝 0) := tendsto_id.const_div_atTop ε
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).add (hq.pow 2))
  have hr : Tendsto (fun x : ℝ => 1 / Real.sqrt (1 + (ε / x) ^ 2)) atTop (𝓝 1) := by
    convert! (tendsto_const_nhds (x := (1 : ℝ))).div hs (by norm_num) using 1
    norm_num
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact ((tanakaSmoothAbs_deriv hε x).trans (tanakaSmoothAbs_positive_ratio ε hx)).symm

theorem tanakaSmoothAbs_deriv_atBot {ε : ℝ} (hε : 0 < ε) :
    Tendsto (deriv (tanakaSmoothAbs ε)) atBot (𝓝 (-1)) := by
  have h := ((tanakaSmoothAbs_deriv_atTop hε).comp tendsto_neg_atBot_atTop).neg
  simpa only [Function.comp_def, tanakaSmoothAbs_deriv_neg hε, neg_neg] using h

theorem tanakaOccupationKernel_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ x, tanakaOccupationKernel ε x) = 1 := by
  have h := integral_of_hasDerivAt_of_tendsto (tanakaOccupationKernel_primitive hε)
    (tanakaOccupationKernel_integrable hε)
    ((tanakaSmoothAbs_deriv_atBot hε).div_const 2) ((tanakaSmoothAbs_deriv_atTop hε).div_const 2)
  norm_num at h
  exact h

end TimeTraps.Analysis
