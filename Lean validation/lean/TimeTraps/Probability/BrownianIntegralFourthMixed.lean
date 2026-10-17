module

public import TimeTraps.Probability.BrownianIntegralFourthMaximal

@[expose] public section

/-! Integrability of the mixed fourth-degree terms, and the zero cubic
moment of an actual Brownian increment, for the finite Gaussian recursion. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_fourth_memLp_of_integrable {f : Ω → ℝ} (hm : AEStronglyMeasurable f P)
    (hi : Integrable (fun ω => f ω ^ 4) P) : MemLp f 4 P := by
  apply (integrable_norm_rpow_iff hm (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  convert! hi using 1
  funext ω
  rw [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]

theorem brownian_fourth_mixed_integrable {A ξ : Ω → ℝ} (hA : MemLp A 4 P) (hξ : MemLp ξ 4 P) :
    Integrable (fun ω => A ω ^ 3 * ξ ω) P ∧
    Integrable (fun ω => A ω ^ 2 * ξ ω ^ 2) P ∧
    Integrable (fun ω => A ω * ξ ω ^ 3) P := by
  have hA2 := brownian_fourth_square_memLp hA
  have hξ2 := brownian_fourth_square_memLp hξ
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_ofNat 2,
      ← ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ← ENNReal.coe_add]
    norm_num⟩
  have hAξ : MemLp (fun ω => A ω * ξ ω) 2 P := by
    change MemLp (A * ξ) 2 P
    exact hξ.mul hA
  constructor
  · convert! hA2.integrable_mul hAξ using 1
    funext ω
    change A ω ^ 3 * ξ ω = A ω ^ 2 * (A ω * ξ ω)
    ring
  constructor
  · exact hA2.integrable_mul hξ2
  · convert! hAξ.integrable_mul hξ2 using 1
    funext ω
    change A ω * ξ ω ^ 3 = (A ω * ξ ω) * ξ ω ^ 2
    ring

theorem brownian_increment_integrable_cube (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    Integrable (fun ω => (B t ω - B s ω) ^ 3) P := by
  have hm : AEStronglyMeasurable (fun ω => (B t ω - B s ω) ^ 3) P :=
    (brownian_increment_memLp hB s t 3 (by norm_num)).aestronglyMeasurable.pow 3
  apply (integrable_norm_iff hm).mp
  simpa only [norm_pow] using
    (brownian_increment_memLp hB s t 3 (by norm_num)).integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)

theorem brownian_increment_cube_moment (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, (B t ω - B s ω) ^ 3 ∂P) = 0 := by
  have hpos := (hB.hasLaw_sub t s).integral_comp (f := fun x : ℝ => x ^ 3) (by fun_prop)
  have hneg := (gaussianReal_neg (hB.hasLaw_sub t s)).integral_comp (f := fun x : ℝ => x ^ 3) (by fun_prop)
  change (∫ ω, (-(B t ω - B s ω)) ^ 3 ∂P) = ∫ z : ℝ, z ^ 3 ∂gaussianReal (-0) (nndist t.val s.val) at hneg
  have he : (fun ω => (-(B t ω - B s ω)) ^ 3) = fun ω => -((B t ω - B s ω) ^ 3) := by
    funext ω
    ring
  rw [he, integral_neg, neg_zero] at hneg
  change (∫ ω, (B t ω - B s ω) ^ 3 ∂P) = _ at hpos
  linarith

theorem brownian_adapted_increment_power_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z) (hiZ : Integrable Z P)
    (k : ℕ) (hk : Integrable (fun ω => (B t ω - B s ω) ^ k) P) :
    Integrable (fun ω => Z ω * (B t ω - B s ω) ^ k) P := by
  have hind := (brownian_adapted_indep_increment hB hBm hst hZ).comp measurable_id
    (show Measurable (fun x : ℝ => x ^ k) by fun_prop)
  exact hind.integrable_mul hiZ hk

theorem brownian_adapted_increment_power_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z) (k : ℕ) :
    (∫ ω, Z ω * (B t ω - B s ω) ^ k ∂P) =
      (∫ ω, Z ω ∂P) * ∫ ω, (B t ω - B s ω) ^ k ∂P := by
  have hind := (brownian_adapted_indep_increment hB hBm hst hZ).comp measurable_id
    (show Measurable (fun x : ℝ => x ^ k) by fun_prop)
  exact hind.integral_fun_mul_eq_mul_integral
    ((hZ.mono ((brownianNaturalFiltration B hBm).le s)).aestronglyMeasurable)
    (((hBm t).sub (hBm s)).pow_const k).aestronglyMeasurable

end TimeTraps.Probability
