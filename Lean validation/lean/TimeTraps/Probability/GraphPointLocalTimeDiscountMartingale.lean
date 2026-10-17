module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountData
public import TimeTraps.Probability.ConditionalIntegral

@[expose] public section

/-! Conditional Fubini identifies the explicit infinite-horizon average
with the conditional expectation of its integrable terminal variable.
Thus it is a genuine martingale in the raw natural graph filtration. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTerminal_condExp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) (t : ℝ≥0) :
    (P.continuousPathLaw hκ x)[P.pointLocalTimeDiscountedTotal a α |
      graphContinuousNaturalFiltration P.geometry t] =ᵐ[P.continuousPathLaw hκ x]
      P.pointLocalTimeDiscountedTerminal a α t := by
  let inst := P.continuousPathLaw_probability hκ x
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ × GraphContinuousPath P.geometry → ℝ := fun q =>
    Real.exp (-(α * q.1)) * P.pointLocalTime a q.1.toNNReal q.2
  let G : ℝ × GraphContinuousPath P.geometry → ℝ := fun q =>
    Real.exp (-(α * q.1)) * P.pointLocalTimeTerminalProcess a q.1.toNNReal t q.2
  have hsection : ∀ᵐ H ∂ν,
      (P.continuousPathLaw hκ x)[fun p => F (H, p) |
        graphContinuousNaturalFiltration P.geometry t] =ᵐ[P.continuousPathLaw hκ x]
      (fun p => G (H, p)) := by
    apply Eventually.of_forall
    intro H
    have hc := condExp_smul (μ := P.continuousPathLaw hκ x) (Real.exp (-(α * H)))
      (P.pointLocalTime a H.toNNReal) (graphContinuousNaturalFiltration P.geometry t)
    have ht := (P.pointLocalTimeTerminalProcess_condExp hκ x a H.toNNReal t).mono
      (fun p hp => congrArg (fun z => Real.exp (-(α * H)) * z) hp)
    filter_upwards [hc, ht] with p hc ht
    simp only [Pi.smul_apply, smul_eq_mul] at hc
    exact hc.trans ht
  have hc := condExp_integral_sections (ν := ν) (P := P.continuousPathLaw hκ x)
    ((graphContinuousNaturalFiltration P.geometry).le t)
    (P.pointLocalTimeDiscount_product_integrable hκ x a hα)
    (P.pointLocalTimeDiscountTerminal_product_integrable hκ x a hα t)
    (P.pointLocalTimeDiscountTerminal_jointlyMeasurable a α t) hsection
  have hs := condExp_smul (μ := P.continuousPathLaw hκ x) α
    (fun p => ∫ H, F (H, p) ∂ν) (graphContinuousNaturalFiltration P.geometry t)
  have he := hc.mono (fun p hp => congrArg (fun z => α * z) hp)
  filter_upwards [hs, he] with p hs he
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  exact hs.trans he

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedTerminal_martingale
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) :
    Martingale (P.pointLocalTimeDiscountedTerminal a α) (graphContinuousNaturalFiltration P.geometry)
      (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (martingale_condExp (P.pointLocalTimeDiscountedTotal a α)
    (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw hκ x)).congr
      (P.pointLocalTimeDiscountedTerminal_stronglyAdapted a α)
      (P.pointLocalTimeDiscountedTerminal_condExp hκ x a hα)

end TimeTraps.Analysis
