module

public import TimeTraps.Probability.BrownianWeightedQuadraticIncrement

@[expose] public section

/-! A raw-left-adapted L² coefficient multiplying a centered squared
increment remains in L². Independence gives the exact diagonal moment;
conditional centering gives orthogonality to every earlier L² variable. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_weightedQuadratic_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) (hξi : Integrable ξ P) :
    Integrable (fun ω => ξ ω * brownianCompensatedSquareIncrement B s t ω) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownian_adapted_indep_compensatedSquare hB hBm hst hξ).integrable_mul hξi
    ((brownianCompensatedSquareIncrement_memLp hB s t).integrable (by norm_num))

theorem brownian_weightedQuadratic_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) (hξi : Integrable ξ P) :
    P[fun ω => ξ ω * brownianCompensatedSquareIncrement B s t ω |
      brownianNaturalFiltration B hBm s] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have h := condExp_mul_of_stronglyMeasurable_left hξ
    (brownian_weightedQuadratic_integrable hB hBm hst hξ hξi)
    ((brownianCompensatedSquareIncrement_memLp hB s t).integrable (by norm_num))
  refine h.trans ?_
  filter_upwards [brownianCompensatedSquareIncrement_condExp hB hBm hst] with ω hω
  simp only [Pi.mul_apply, hω, Pi.zero_apply, mul_zero]

theorem brownian_weightedQuadratic_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) (hξi : Integrable ξ P) :
    (∫ ω, ξ ω * brownianCompensatedSquareIncrement B s t ω ∂P) = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∫ ω, P[fun ω => ξ ω * brownianCompensatedSquareIncrement B s t ω |
        brownianNaturalFiltration B hBm s] ω ∂P :=
      (integral_condExp ((brownianNaturalFiltration B hBm).le s)).symm
    _ = ∫ _ : Ω, (0 : ℝ) ∂P := integral_congr_ae
      (brownian_weightedQuadratic_condExp hB hBm hst hξ hξi)
    _ = 0 := integral_zero _ _

theorem brownian_weightedQuadratic_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) (hξ2 : MemLp ξ 2 P) :
    MemLp (fun ω => ξ ω * brownianCompensatedSquareIncrement B s t ω) 2 P := by
  have hq := brownianCompensatedSquareIncrement_memLp hB s t
  have hind := (brownian_adapted_indep_compensatedSquare hB hBm hst hξ).comp
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
  have hi := hind.integrable_mul hξ2.integrable_sq hq.integrable_sq
  apply (memLp_two_iff_integrable_sq (hξ2.aestronglyMeasurable.mul hq.aestronglyMeasurable)).mpr
  change Integrable (fun ω => ξ ω ^ 2 * brownianCompensatedSquareIncrement B s t ω ^ 2) P at hi
  change Integrable (fun ω => (ξ ω * brownianCompensatedSquareIncrement B s t ω) ^ 2) P
  simpa only [mul_pow] using hi

theorem brownian_weightedQuadratic_secondMoment (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ) (hξ2 : MemLp ξ 2 P) :
    (∫ ω, (ξ ω * brownianCompensatedSquareIncrement B s t ω) ^ 2 ∂P) =
      2 * (t.val - s.val) ^ 2 * ∫ ω, ξ ω ^ 2 ∂P := by
  have hq := brownianCompensatedSquareIncrement_memLp hB s t
  have hind := (brownian_adapted_indep_compensatedSquare hB hBm hst hξ).comp
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
  calc
    _ = (∫ ω, ξ ω ^ 2 ∂P) * ∫ ω, brownianCompensatedSquareIncrement B s t ω ^ 2 ∂P := by
      simpa only [Function.comp_def, mul_pow] using hind.integral_fun_mul_eq_mul_integral
        hξ2.integrable_sq.aestronglyMeasurable hq.integrable_sq.aestronglyMeasurable
    _ = _ := by rw [brownianCompensatedSquareIncrement_secondMoment hB hst, mul_comm]

theorem brownian_weightedQuadratic_orthogonal (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {Z ξ : Ω → ℝ}
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z)
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hZ2 : MemLp Z 2 P) (hξ2 : MemLp ξ 2 P) :
    (∫ ω, Z ω * (ξ ω * brownianCompensatedSquareIncrement B s t ω) ∂P) = 0 := by
  have h := brownian_weightedQuadratic_mean hB hBm hst (hZ.mul hξ) (hZ2.integrable_mul hξ2)
  simpa only [Pi.mul_apply, mul_assoc] using h

end TimeTraps.Probability
