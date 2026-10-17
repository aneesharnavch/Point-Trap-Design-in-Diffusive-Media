module

public import TimeTraps.Probability.BrownianConstruction
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.ConditionalExpectation

@[expose] public section

/-! The raw natural filtration of the constructed Brownian process and
independence of future increments from its past. No completion or
right-continuity of the filtration is asserted here. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def brownianNaturalFiltration (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t)) :
    Filtration ℝ≥0 mΩ := Filtration.natural B (fun t => (hBm t).stronglyMeasurable)

theorem brownianNaturalFiltration_stronglyAdapted (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) : StronglyAdapted (brownianNaturalFiltration B hBm) B :=
  Filtration.stronglyAdapted_natural (fun t => (hBm t).stronglyMeasurable)

theorem brownianNaturalFiltration_eq_comap (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (s : ℝ≥0) :
    brownianNaturalFiltration B hBm s =
      MeasurableSpace.comap (fun ω (t : Iic s) => B t ω) inferInstance :=
  Filtration.natural_eq_comap B (fun t => (hBm t).stronglyMeasurable) s

theorem brownian_increment_indep_past {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω => B t ω - B s ω) (fun ω (u : Iic s) => B u ω) P := by
  have h := (hB.indepFun_shift s).comp
    (measurable_pi_apply (t - s)) measurable_id
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using h

theorem brownian_increment_indep_natural {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance)
      (brownianNaturalFiltration B hBm s) P := by
  rw [brownianNaturalFiltration_eq_comap]
  exact brownian_increment_indep_past hB hst

theorem brownian_increment_function_condExp {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {s t : ℝ≥0} (hst : s ≤ t) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    P[fun ω => φ (B t ω - B s ω) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun _ => ∫ ω, φ (B t ω - B s ω) ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact condExp_indep_eq ((hBm t).sub (hBm s)).comap_le
    ((brownianNaturalFiltration B hBm).le s)
    (hφ.comp (comap_measurable (fun ω => B t ω - B s ω))).stronglyMeasurable
    (brownian_increment_indep_natural hB hBm hst)

theorem brownian_increment_condExp {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => B t ω - B s ω | brownianNaturalFiltration B hBm s] =ᵐ[P] 0 := by
  have h := brownian_increment_function_condExp hB hBm hst id measurable_id
  simpa only [id_eq, integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
    hB.integral_eval, sub_self, Pi.zero_def] using h

noncomputable def brownianFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  brownianNaturalFiltration brownianDyadicPath brownianDyadicPath_measurable

theorem brownianFiltration_stronglyAdapted : StronglyAdapted brownianFiltration brownianDyadicPath :=
  brownianNaturalFiltration_stronglyAdapted brownianDyadicPath brownianDyadicPath_measurable

end TimeTraps.Probability
