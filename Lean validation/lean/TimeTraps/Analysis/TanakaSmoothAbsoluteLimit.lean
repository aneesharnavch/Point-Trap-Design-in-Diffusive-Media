module

public import TimeTraps.Analysis.TanakaSmoothAbsoluteShift
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Real.Sign

@[expose] public section

/-! Genuine limits of smooth absolute values and their slopes. At the
center all slopes are zero, so no exceptional-level hypothesis is needed. -/

namespace TimeTraps.Analysis

open Filter
open scoped Topology

noncomputable def tanakaSmoothingScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem tanakaSmoothingScale_pos (n : ℕ) : 0 < tanakaSmoothingScale n := by
  unfold tanakaSmoothingScale
  positivity

theorem tanakaSmoothingScale_tendsto :
    Tendsto tanakaSmoothingScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem tanakaSmoothAbs_tendsto {ε : ℕ → ℝ}
    (hlim : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => tanakaSmoothAbs (ε n) x) atTop (𝓝 |x|) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := x ^ 2)).add (hlim.pow 2))
  simpa only [tanakaSmoothAbs, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    add_zero, Real.sqrt_sq_eq_abs, Function.comp_def] using h

theorem tanakaSmoothAbs_deriv_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => deriv (tanakaSmoothAbs (ε n)) x) atTop (𝓝 (Real.sign x)) := by
  have hf : (fun n => deriv (tanakaSmoothAbs (ε n)) x) =
      fun n => x / tanakaSmoothAbs (ε n) x :=
    funext fun n => tanakaSmoothAbs_deriv (hε n) x
  rw [hf]
  by_cases hx : x = 0
  · simp only [hx, zero_div, Real.sign_zero]
    exact tendsto_const_nhds
  · have he : Real.sign x = x / |x| := by
      rcases lt_or_gt_of_ne hx with hn | hp
      · rw [Real.sign_of_neg hn, abs_of_neg hn]
        field_simp
      · rw [Real.sign_of_pos hp, abs_of_pos hp, div_self hx]
    rw [he]
    exact tendsto_const_nhds.div (tanakaSmoothAbs_tendsto hlim x) (abs_ne_zero.mpr hx)

theorem tanakaSmoothShift_deriv_tendsto (a x : ℝ) :
    Tendsto (fun n => deriv (tanakaSmoothShift (tanakaSmoothingScale n) a) x)
      atTop (𝓝 (Real.sign (x - a))) := by
  simp only [tanakaSmoothShift_deriv]
  exact tanakaSmoothAbs_deriv_tendsto tanakaSmoothingScale_pos tanakaSmoothingScale_tendsto (x - a)

theorem tanakaSmoothShift_tendsto (a x : ℝ) :
    Tendsto (fun n => tanakaSmoothShift (tanakaSmoothingScale n) a x) atTop (𝓝 |x - a|) :=
  tanakaSmoothAbs_tendsto tanakaSmoothingScale_tendsto (x - a)

end TimeTraps.Analysis
