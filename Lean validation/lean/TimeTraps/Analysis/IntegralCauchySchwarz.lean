module

public import TimeTraps.Analysis.IntervalEnergy

@[expose] public section

/-!
Cauchy--Schwarz for actual square-integrable real functions, transported
from Mathlib's independently constructed L2 inner-product space.
-/

namespace TimeTraps.Analysis

open MeasureTheory

theorem memLp_inner_toLp_eq_integral_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [hfx, hgx, Real.inner_apply]

theorem memLp_norm_toLp_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, memLp_inner_toLp_eq_integral_mul hf hf]
  simp only [pow_two]

theorem memLp_integral_mul_sq_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  rw [memLp_inner_toLp_eq_integral_mul hf hg, Real.norm_eq_abs] at h
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow, memLp_norm_toLp_sq hf, memLp_norm_toLp_sq hg] using hs

theorem interval_integral_mul_sq_le {f g : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hf : MemLp f 2 (volume.restrict (Set.uIoc l r)))
    (hg : MemLp g 2 (volume.restrict (Set.uIoc l r))) :
    (∫ x in l..r, f x * g x) ^ 2 ≤
      (∫ x in l..r, f x ^ 2) * (∫ x in l..r, g x ^ 2) := by
  simpa only [intervalIntegral.integral_of_le hlr, Set.uIoc_of_le hlr] using
    memLp_integral_mul_sq_le hf hg

end TimeTraps.Analysis
