module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Scalar estimates for differentiating the heat series.  Positive spectral
values give a uniform reciprocal bound for slopes on nonnegative time. -/

namespace TimeTraps.Analysis

open Set

theorem compactHeatScalar_hasDerivAt (μ s : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-t / μ)) (-μ⁻¹ * Real.exp (-s / μ)) s := by
  simpa only [Pi.neg_apply, id_eq, neg_div, one_div, mul_comm] using
    (((hasDerivAt_id s).neg.div_const μ).exp)

theorem compactHeatScalar_derivative_bound {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) :
    ‖-μ⁻¹ * Real.exp (-s / μ)‖ ≤ μ⁻¹ := by
  rw [norm_mul, norm_neg, Real.norm_of_nonneg (inv_nonneg.mpr hμ.le),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_of_le_one_right (inv_nonneg.mpr hμ.le)
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hμ.le)

theorem compactHeatScalar_lipschitz {μ s t : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-t / μ) - Real.exp (-s / μ)| ≤ μ⁻¹ * |t - s| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x (_ : x ∈ Ici (0 : ℝ)) => (compactHeatScalar_hasDerivAt μ x).hasDerivWithinAt)
      (fun x hx => compactHeatScalar_derivative_bound hμ hx)
      (convex_Ici (0 : ℝ)) hs ht

theorem compactHeatScalar_slope_bound {μ s t : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |slope (fun r : ℝ => Real.exp (-r / μ)) s t| ≤ μ⁻¹ := by
  by_cases hts : t = s
  · subst t
    simp only [slope_def_field, sub_self, div_zero, abs_zero]
    exact inv_nonneg.mpr hμ.le
  · rw [slope_def_field, abs_div]
    exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hts))).mpr
      (compactHeatScalar_lipschitz hμ hs ht)

theorem compactHeatScalar_slope_error_bound {μ s t : ℝ}
    (hμ : 0 < μ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |slope (fun r : ℝ => Real.exp (-r / μ)) s t + μ⁻¹ * Real.exp (-s / μ)| ≤ 2 * μ⁻¹ := by
  have hd : |μ⁻¹ * Real.exp (-s / μ)| ≤ μ⁻¹ := by
    simpa only [Real.norm_eq_abs, neg_mul, abs_neg] using
      compactHeatScalar_derivative_bound hμ hs
  calc
    _ ≤ |slope (fun r : ℝ => Real.exp (-r / μ)) s t| + |μ⁻¹ * Real.exp (-s / μ)| :=
      abs_add_le _ _
    _ ≤ μ⁻¹ + μ⁻¹ := add_le_add (compactHeatScalar_slope_bound hμ hs ht) hd
    _ = 2 * μ⁻¹ := by ring

end TimeTraps.Analysis
