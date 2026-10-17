module

public import TimeTraps.Probability.BrownianStepIntegralIncrement
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-! A left-measurable unit sign preserves the conditional law of the
next centered Gaussian Brownian increment. The proof splits its two
possible signs and uses actual increment independence and Gaussian
symmetry; no transformed-process law is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_increment_complex_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    (φ : ℝ → ℂ) (hφ : Measurable φ) :
    P[fun ω => φ (B t ω - B s ω) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun _ => ∫ ω, φ (B t ω - B s ω) ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact condExp_indep_eq ((hBm t).sub (hBm s)).comap_le
    ((brownianNaturalFiltration B hBm).le s)
    (hφ.comp (comap_measurable (fun ω => B t ω - B s ω))).stronglyMeasurable
    (brownian_increment_indep_natural hB hBm hst)

theorem brownian_increment_neg_test_integral (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (φ : ℝ → ℂ) (hφ : Measurable φ) :
    (∫ ω, φ (-(B t ω - B s ω)) ∂P) = ∫ ω, φ (B t ω - B s ω) ∂P := by
  have hp := (hB.hasLaw_sub t s).integral_comp hφ.aestronglyMeasurable
  have hn := (gaussianReal_neg (hB.hasLaw_sub t s)).integral_comp hφ.aestronglyMeasurable
  simp only [neg_zero] at hn
  simpa only [Function.comp_def, Pi.neg_apply, Pi.sub_apply] using hn.trans hp.symm

theorem brownian_predictable_sign_test_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hunit : ∀ᵐ ω ∂P, |ξ ω| = 1) (φ : ℝ → ℂ) (hφ : Measurable φ)
    {M : ℝ} (hb : ∀ z, ‖φ z‖ ≤ M) :
    P[fun ω => φ (ξ ω * (B t ω - B s ω)) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun _ => ∫ z, φ z ∂gaussianReal 0 (nndist t.val s.val) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let A : Set Ω := {ω | ξ ω = 1}
  let f : Ω → ℂ := fun ω => φ (B t ω - B s ω)
  let g : Ω → ℂ := fun ω => φ (-(B t ω - B s ω))
  have hA : MeasurableSet[brownianNaturalFiltration B hBm s] A := measurableSet_eq_fun hξ.measurable measurable_const
  have hA₀ : MeasurableSet A := ((brownianNaturalFiltration B hBm).le s) A hA
  have hf : Integrable f P := (integrable_const M).mono'
    (hφ.comp ((hBm t).sub (hBm s))).aestronglyMeasurable (Eventually.of_forall (fun ω => hb _))
  have hg : Integrable g P := (integrable_const M).mono'
    (hφ.comp ((hBm t).sub (hBm s)).neg).aestronglyMeasurable (Eventually.of_forall (fun ω => hb _))
  have he : (fun ω => φ (ξ ω * (B t ω - B s ω))) =ᵐ[P] A.indicator f + Aᶜ.indicator g := by
    filter_upwards [hunit] with ω hu
    by_cases ha : ω ∈ A
    · have hξone : ξ ω = 1 := ha
      simp only [Pi.add_apply, indicator_of_mem ha, indicator_of_notMem (show ω ∉ Aᶜ from fun hc => hc ha),
        add_zero, hξone, one_mul]
      rfl
    · have hξneg : ξ ω = -1 := by
        by_cases hp : 0 ≤ ξ ω
        · rw [abs_of_nonneg hp] at hu
          exact (ha hu).elim
        · rw [abs_of_nonpos (le_of_not_ge hp)] at hu
          linarith
      simp only [Pi.add_apply, indicator_of_notMem ha, indicator_of_mem (show ω ∈ Aᶜ from ha),
        zero_add, hξneg, neg_one_mul]
      rfl
  have hcf := brownian_increment_complex_condExp hB hBm hst φ hφ
  have hcg := brownian_increment_complex_condExp hB hBm hst (fun z => φ (-z)) (hφ.comp measurable_neg)
  have hs := brownian_increment_neg_test_integral hB s t φ hφ
  change P[f | brownianNaturalFiltration B hBm s] =ᵐ[P] (fun _ => ∫ ω, f ω ∂P) at hcf
  change P[g | brownianNaturalFiltration B hBm s] =ᵐ[P] (fun _ => ∫ ω, g ω ∂P) at hcg
  change (∫ ω, g ω ∂P) = ∫ ω, f ω ∂P at hs
  have hm : (∫ ω, f ω ∂P) = ∫ z, φ z ∂gaussianReal 0 (nndist t.val s.val) :=
    (hB.hasLaw_sub t s).integral_comp hφ.aestronglyMeasurable
  refine (condExp_congr_ae he).trans ((condExp_add (hf.indicator hA₀) (hg.indicator hA₀.compl) (brownianNaturalFiltration B hBm s)).trans ?_)
  filter_upwards [condExp_indicator hf hA, condExp_indicator hg hA.compl, hcf, hcg]
    with ω hi hj hfi hgi
  change P[A.indicator f | brownianNaturalFiltration B hBm s] ω + P[Aᶜ.indicator g | brownianNaturalFiltration B hBm s] ω = _
  rw [hi, hj]
  by_cases ha : ω ∈ A
  · rw [indicator_of_mem ha, indicator_of_notMem (show ω ∉ Aᶜ from fun hc => hc ha), add_zero, hfi, hm]
  · rw [indicator_of_notMem ha, indicator_of_mem (show ω ∈ Aᶜ from ha), zero_add, hgi, hs, hm]

end TimeTraps.Probability
