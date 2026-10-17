module

public import TimeTraps.Probability.BrownianMartingaleSquare
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-! A square-integrable coefficient measurable at the left endpoint can
multiply a future Brownian increment without losing square integrability.
Independence supplies this fact without a bounded-coefficient hypothesis. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_adapted_indep_increment (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) :
    IndepFun ξ (fun ω => B t ω - B s ω) P :=
  indep_of_indep_of_le_left (brownian_increment_indep_natural hB hBm hst).symm
    hξ.measurable.comap_le

theorem brownian_weighted_increment_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hξi : Integrable ξ P) : Integrable (fun ω => ξ ω * (B t ω - B s ω)) P :=
  (brownian_adapted_indep_increment hB hBm hst hξ).integrable_mul hξi
    ((hB.integrable_eval t).sub (hB.integrable_eval s))

theorem brownian_weighted_increment_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hξi : Integrable ξ P) :
    P[fun ω => ξ ω * (B t ω - B s ω) | brownianNaturalFiltration B hBm s] =ᵐ[P] 0 := by
  have h := condExp_mul_of_stronglyMeasurable_left hξ
    (brownian_weighted_increment_integrable hB hBm hst hξ hξi)
    ((hB.integrable_eval t).sub (hB.integrable_eval s))
  refine h.trans ?_
  filter_upwards [brownian_increment_condExp hB hBm hst] with ω hω
  simp only [Pi.mul_apply, hω, Pi.zero_apply, mul_zero]

theorem brownian_weighted_increment_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hξi : Integrable ξ P) : (∫ ω, ξ ω * (B t ω - B s ω) ∂P) = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∫ ω, P[fun ω => ξ ω * (B t ω - B s ω) |
        brownianNaturalFiltration B hBm s] ω ∂P :=
      (integral_condExp ((brownianNaturalFiltration B hBm).le s)).symm
    _ = ∫ _ : Ω, (0 : ℝ) ∂P := integral_congr_ae
      (brownian_weighted_increment_condExp hB hBm hst hξ hξi)
    _ = 0 := integral_zero _ _

theorem brownian_weighted_increment_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hξ2 : MemLp ξ 2 P) : MemLp (fun ω => ξ ω * (B t ω - B s ω)) 2 P := by
  have hind := (brownian_adapted_indep_increment hB hBm hst hξ).comp
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
  have hi := hind.integrable_mul hξ2.integrable_sq
    (brownian_increment_integrable_sq hB s t)
  change Integrable (fun ω => ξ ω ^ 2 * (B t ω - B s ω) ^ 2) P at hi
  apply (memLp_two_iff_integrable_sq
    (hξ2.aestronglyMeasurable.mul ((hBm t).sub (hBm s)).aestronglyMeasurable)).mpr
  change Integrable (fun ω => (ξ ω * (B t ω - B s ω)) ^ 2) P
  simpa only [mul_pow] using hi

theorem brownian_weighted_increment_square_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hξ2 : MemLp ξ 2 P) :
    P[fun ω => (ξ ω * (B t ω - B s ω)) ^ 2 |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => ξ ω ^ 2 * (t.val - s.val) := by
  have hi := (brownian_weighted_increment_memLp hB hBm hst hξ hξ2).integrable_sq
  have hip : Integrable ((fun ω => ξ ω ^ 2) * (fun ω => (B t ω - B s ω) ^ 2)) P := by
    change Integrable (fun ω => ξ ω ^ 2 * (B t ω - B s ω) ^ 2) P
    simpa only [mul_pow] using hi
  have h := condExp_mul_of_stronglyMeasurable_left (f := fun ω => ξ ω ^ 2) (hξ.pow 2) hip
    (brownian_increment_integrable_sq hB s t)
  have he : (fun ω => ξ ω ^ 2) * (fun ω => (B t ω - B s ω) ^ 2) =
      (fun ω => (ξ ω * (B t ω - B s ω)) ^ 2) := by
    funext ω
    simp only [Pi.mul_apply, mul_pow]
  rw [he] at h
  refine h.trans ?_
  filter_upwards [brownian_increment_square_condExp hB hBm hst] with ω hω
  change ξ ω ^ 2 * P[fun ω => (B t ω - B s ω) ^ 2 |
    brownianNaturalFiltration B hBm s] ω = _
  rw [hω]

theorem brownian_weighted_increment_second_moment (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hξ2 : MemLp ξ 2 P) :
    (∫ ω, (ξ ω * (B t ω - B s ω)) ^ 2 ∂P) =
      (t.val - s.val) * ∫ ω, ξ ω ^ 2 ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∫ ω, P[fun ω => (ξ ω * (B t ω - B s ω)) ^ 2 |
        brownianNaturalFiltration B hBm s] ω ∂P :=
      (integral_condExp ((brownianNaturalFiltration B hBm).le s)).symm
    _ = ∫ ω, ξ ω ^ 2 * (t.val - s.val) ∂P := integral_congr_ae
      (brownian_weighted_increment_square_condExp hB hBm hst hξ hξ2)
    _ = _ := by rw [integral_mul_const, mul_comm]

end TimeTraps.Probability
