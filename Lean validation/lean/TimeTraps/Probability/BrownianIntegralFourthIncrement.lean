module

public import TimeTraps.Probability.BrownianStepIntegralIncrement

@[expose] public section

/-! Exact fourth conditional moments of the genuine Brownian stochastic
increment with an arbitrary adapted L4 coefficient. These are the finite
Gaussian ingredients for a later maximal fourth-moment estimate. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_memLp_four_integrable_fourth {ξ : Ω → ℝ} (hξ : MemLp ξ 4 P) :
    Integrable (fun ω => ξ ω ^ 4) P := by
  have hi := hξ.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  simpa only [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.norm_eq_abs, sq_abs] using hi

theorem brownian_increment_integrable_fourth (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    Integrable (fun ω => (B t ω - B s ω) ^ 4) P :=
  brownian_memLp_four_integrable_fourth (brownian_increment_memLp hB s t 4 (by norm_num))

theorem brownian_increment_fourth_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => (B t ω - B s ω) ^ 4 | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun _ => 3 * (t.val - s.val) ^ 2 := by
  have h := brownian_increment_function_condExp hB hBm hst (fun x => x ^ 4) (by fun_prop)
  rw [brownian_increment_fourth_moment hB s t,
    abs_of_nonneg (sub_nonneg.mpr (show s.val ≤ t.val from hst))] at h
  exact h

theorem brownian_weighted_increment_integrable_fourth (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) (hξ4 : MemLp ξ 4 P) :
    Integrable (fun ω => (ξ ω * (B t ω - B s ω)) ^ 4) P := by
  have hind := (brownian_adapted_indep_increment hB hBm hst hξ).comp
    (show Measurable (fun x : ℝ => x ^ 4) by fun_prop)
    (show Measurable (fun x : ℝ => x ^ 4) by fun_prop)
  have hi := hind.integrable_mul (brownian_memLp_four_integrable_fourth hξ4)
    (brownian_increment_integrable_fourth hB s t)
  change Integrable (fun ω => ξ ω ^ 4 * (B t ω - B s ω) ^ 4) P at hi
  simpa only [mul_pow] using hi

theorem brownian_weighted_increment_fourth_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) (hξ4 : MemLp ξ 4 P) :
    P[fun ω => (ξ ω * (B t ω - B s ω)) ^ 4 | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => ξ ω ^ 4 * (3 * (t.val - s.val) ^ 2) := by
  have hi := brownian_weighted_increment_integrable_fourth hB hBm hst hξ hξ4
  have hip : Integrable ((fun ω => ξ ω ^ 4) * (fun ω => (B t ω - B s ω) ^ 4)) P := by
    change Integrable (fun ω => ξ ω ^ 4 * (B t ω - B s ω) ^ 4) P
    simpa only [mul_pow] using hi
  have h := condExp_mul_of_stronglyMeasurable_left (f := fun ω => ξ ω ^ 4) (hξ.pow 4) hip
    (brownian_increment_integrable_fourth hB s t)
  have he : (fun ω => ξ ω ^ 4) * (fun ω => (B t ω - B s ω) ^ 4) =
      (fun ω => (ξ ω * (B t ω - B s ω)) ^ 4) := by
    funext ω
    simp only [Pi.mul_apply, mul_pow]
  rw [he] at h
  refine h.trans ?_
  filter_upwards [brownian_increment_fourth_condExp hB hBm hst] with ω hω
  change ξ ω ^ 4 * P[fun ω => (B t ω - B s ω) ^ 4 | brownianNaturalFiltration B hBm s] ω = _
  rw [hω]

theorem brownian_weighted_increment_fourth_moment (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) (hξ4 : MemLp ξ 4 P) :
    (∫ ω, (ξ ω * (B t ω - B s ω)) ^ 4 ∂P) =
      3 * (t.val - s.val) ^ 2 * ∫ ω, ξ ω ^ 4 ∂P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∫ ω, P[fun ω => (ξ ω * (B t ω - B s ω)) ^ 4 | brownianNaturalFiltration B hBm s] ω ∂P :=
      (integral_condExp ((brownianNaturalFiltration B hBm).le s)).symm
    _ = ∫ ω, ξ ω ^ 4 * (3 * (t.val - s.val) ^ 2) ∂P :=
      integral_congr_ae (brownian_weighted_increment_fourth_condExp hB hBm hst hξ hξ4)
    _ = _ := by rw [integral_mul_const, mul_comm]

end TimeTraps.Probability
