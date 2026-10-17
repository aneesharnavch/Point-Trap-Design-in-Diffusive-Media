module

public import TimeTraps.Probability.BrownianConstruction
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Exact integrability and Gaussian increment moments used in the Brownian
martingale and quadratic-variation calculations. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_increment_memLp (hB : IsPreBrownianReal B P) (s t : ℝ≥0)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (fun ω => B t ω - B s ω) p P :=
  (hB.hasLaw_sub t s).hasGaussianLaw.memLp hp

theorem brownian_eval_integrable_sq (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Integrable (fun ω => B t ω ^ 2) P := (hB.hasLaw_eval t).hasGaussianLaw.memLp_two.integrable_sq

theorem brownian_increment_integrable_sq (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    Integrable (fun ω => (B t ω - B s ω) ^ 2) P :=
  (brownian_increment_memLp hB s t 2 (by norm_num)).integrable_sq

theorem brownian_increment_mean (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, B t ω - B s ω ∂P) = 0 := by
  rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
    hB.integral_eval, hB.integral_eval, sub_self]

theorem brownian_increment_second_moment (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = |t.val - s.val| := by
  have h := (hB.hasLaw_sub t s).variance_eq
  rw [variance_eq_integral (hB.hasLaw_sub t s).aemeasurable, variance_id_gaussianReal] at h
  have hm : (∫ ω, (B t - B s) ω ∂P) = 0 := brownian_increment_mean hB s t
  rw [hm] at h
  calc
    _ = (nndist t.val s.val : ℝ) := by simpa only [sub_zero, Pi.sub_apply] using h
    _ = _ := by change dist t.val s.val = _; rw [Real.dist_eq]

theorem brownian_increment_fourth_moment (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, (B t ω - B s ω) ^ 4 ∂P) = 3 * |t.val - s.val| ^ 2 := by
  calc
    _ = ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 (nndist t.val s.val) :=
      (hB.hasLaw_sub t s).integral_comp (by fun_prop)
    _ = 3 * (nndist t.val s.val : ℝ) ^ 2 := gaussianReal_fourth_moment _
    _ = _ := by change 3 * (dist t.val s.val) ^ 2 = _; rw [Real.dist_eq]

end TimeTraps.Probability
