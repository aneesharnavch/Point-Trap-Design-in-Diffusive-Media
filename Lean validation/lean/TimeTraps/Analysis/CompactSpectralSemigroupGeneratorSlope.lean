module

public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorDomain
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorScalar

@[expose] public section

/-! Exact coefficient and norm identities for difference quotients on the
actual inverse domain, together with their square-summable dominating bound. -/

namespace TimeTraps.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.heatCurve_slope_error_inner {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i)
      (slope (h.heatCurve (x : E)) s t + h.heatCurve (inverseOperator T h.injective x) s) =
      (slope (fun r : ℝ => Real.exp (-r / i.1)) s t + i.1⁻¹ * Real.exp (-s / i.1)) *
        inner ℝ (h.eigenbasis i) (x : E) := by
  rw [slope_def_module, inner_add_right, inner_smul_right, inner_sub_right,
    h.heatCurve_inner _ ht, h.heatCurve_inner _ hs, h.heatCurve_inner _ hs,
    h.inner_eigenbasis_inverse, slope_def_field, div_eq_mul_inv]
  ring

theorem CompactPositiveInverse.heatCurve_slope_error_sq {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖slope (h.heatCurve (x : E)) s t + h.heatCurve (inverseOperator T h.injective x) s‖ ^ 2 =
      ∑' i : CompactSpectralIndex T,
        ((slope (fun r : ℝ => Real.exp (-r / i.1)) s t + i.1⁻¹ * Real.exp (-s / i.1)) *
          inner ℝ (h.eigenbasis i) (x : E)) ^ 2 := by
  rw [← h.parseval]
  apply tsum_congr
  intro i
  rw [h.heatCurve_slope_error_inner x hs ht]

theorem CompactPositiveInverse.heatCurve_slope_error_bound {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (i : CompactSpectralIndex T) :
    ‖((slope (fun r : ℝ => Real.exp (-r / i.1)) s t + i.1⁻¹ * Real.exp (-s / i.1)) *
      inner ℝ (h.eigenbasis i) (x : E)) ^ 2‖ ≤
        4 * (i.1⁻¹ * inner ℝ (h.eigenbasis i) (x : E)) ^ 2 := by
  let a := slope (fun r : ℝ => Real.exp (-r / i.1)) s t + i.1⁻¹ * Real.exp (-s / i.1)
  let c := inner ℝ (h.eigenbasis i) (x : E)
  change ‖(a * c) ^ 2‖ ≤ 4 * (i.1⁻¹ * c) ^ 2
  have ha : |a| ≤ 2 * i.1⁻¹ := compactHeatScalar_slope_error_bound (h.eigenbasis_positive i) hs ht
  have hmul : |a * c| ≤ 2 * |i.1⁻¹ * c| := by
    rw [abs_mul, abs_mul, abs_of_pos (h.reciprocal_positive i)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ha (abs_nonneg c)
  have hsquare := (sq_le_sq₀ (abs_nonneg (a * c))
    (show 0 ≤ 2 * |i.1⁻¹ * c| by positivity)).mpr hmul
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (a * c), sq_abs (i.1⁻¹ * c)]

end TimeTraps.Analysis
