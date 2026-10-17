module

public import TimeTraps.Analysis.IntervalEnergyLocal
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
Quantitative one-dimensional Sobolev estimates for the independent AC/L2
energy class. The estimates apply to all signed energy functions, including
their endpoint values, and use the actual square integral of the derivative.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

/-- Cauchy--Schwarz against the constant function, proved by integrating a
nonnegative square. Both integrability hypotheses are actual L1 statements. -/
theorem interval_integral_sq_le_length_mul {f : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hf₂ : IntervalIntegrable (fun x => f x ^ 2) volume l r) :
    (∫ x in l..r, f x) ^ 2 ≤ (r - l) * (∫ x in l..r, f x ^ 2) := by
  rcases hlr.eq_or_lt with heq | hlt
  · subst r
    simp
  let L := r - l
  let I := ∫ x in l..r, f x
  have hL : 0 < L := sub_pos.mpr hlt
  have he : (fun x => (L * f x - I) ^ 2) =
      fun x => (L ^ 2 * f x ^ 2 - (2 * L * I) * f x) + I ^ 2 := by
    funext x
    ring
  have hi : (∫ x in l..r, (L * f x - I) ^ 2) =
      L * (L * (∫ x in l..r, f x ^ 2) - I ^ 2) := by
    rw [he, intervalIntegral.integral_add
      ((hf₂.const_mul (L ^ 2)).sub (hf.const_mul (2 * L * I)))
      intervalIntegrable_const,
      intervalIntegral.integral_sub (hf₂.const_mul (L ^ 2))
      (hf.const_mul (2 * L * I))]
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      smul_eq_mul]
    change L ^ 2 * (∫ x in l..r, f x ^ 2) - (2 * L * I) * I + L * I ^ 2 = _
    ring
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hlr
    (fun x => sq_nonneg (L * f x - I))
  rw [hi] at hn
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hL).mp hn)

/-- The squared oscillation bound on an ordered subinterval. -/
theorem IntervalEnergy.sub_sq_le_of_le {u : ℝ → ℝ} {l r x y : ℝ}
    (hu : IntervalEnergy u l r) (hx : x ∈ Icc l r) (hy : y ∈ Icc l r)
    (hxy : x ≤ y) :
    (u y - u x) ^ 2 ≤ (y - x) * (∫ t in l..r, deriv u t ^ 2) := by
  have hlr : l ≤ r := hx.1.trans hx.2
  have hsub : uIcc x y ⊆ uIcc l r := by
    rw [uIcc_of_le hxy, uIcc_of_le hlr]
    exact Icc_subset_Icc hx.1 hy.2
  have hv := hu.mono hsub
  have hcs := interval_integral_sq_le_length_mul hxy
    hv.absolutelyContinuous.intervalIntegrable_deriv hv.derivative_square_integrable
  rw [hv.absolutelyContinuous.integral_deriv_eq_sub] at hcs
  have hm : (∫ t in x..y, deriv u t ^ 2) ≤ ∫ t in l..r, deriv u t ^ 2 :=
    intervalIntegral.integral_mono_interval hx.1 hxy hy.2
      (Filter.Eventually.of_forall fun t => sq_nonneg (deriv u t))
      hu.derivative_square_integrable
  exact hcs.trans (mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hxy))

/-- The squared half-Hölder estimate, with no ordering of the evaluation sites. -/
theorem IntervalEnergy.sub_sq_le {u : ℝ → ℝ} {l r x y : ℝ}
    (hu : IntervalEnergy u l r) (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) :
    (u x - u y) ^ 2 ≤ |x - y| * (∫ t in l..r, deriv u t ^ 2) := by
  rcases le_total y x with hyx | hxy
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hyx)] using hu.sub_sq_le_of_le hy hx hyx
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub, sub_sq_comm] using
      hu.sub_sq_le_of_le hx hy hxy

/-- The half-Hölder estimate in the manuscript, including both endpoints. -/
theorem IntervalEnergy.abs_sub_le_sqrt {u : ℝ → ℝ} {l r x y : ℝ}
    (hu : IntervalEnergy u l r) (hx : x ∈ Icc l r) (hy : y ∈ Icc l r) :
    |u x - u y| ≤ Real.sqrt |x - y| * Real.sqrt (∫ t in l..r, deriv u t ^ 2) := by
  have hE : 0 ≤ ∫ t in l..r, deriv u t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (hx.1.trans hx.2) (fun t => sq_nonneg _)
  have h := hu.sub_sq_le hx hy
  have hsx := Real.sq_sqrt (abs_nonneg (x - y))
  have hsE := Real.sq_sqrt hE
  have hprod : (Real.sqrt |x - y| * Real.sqrt (∫ t in l..r, deriv u t ^ 2)) ^ 2 =
      |x - y| * (∫ t in l..r, deriv u t ^ 2) := by
    rw [mul_pow, hsx, hsE]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  simpa only [sq_abs, hprod] using h

end TimeTraps.Analysis
