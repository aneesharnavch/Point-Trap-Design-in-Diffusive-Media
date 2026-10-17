module

public import TimeTraps.Probability.GraphBorelResolventConditional
public import TimeTraps.Probability.GraphBorelResolventDecomposition

@[expose] public section

/-! The actual discounted resolvent martingale for every bounded Borel
graph forcing, derived from the original path law and raw Markov property. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.borelDiscountedResolvent
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (α : ℝ) (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  P.borelDiscountedPast f α t p + Real.exp (-α * (t : ℝ)) * P.borelTransitionLaplace f α (p t)

theorem GraphShiftedContactOperatorProblem.borelDiscountedResolvent_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (f : GraphRealization P.geometry → ℝ) (hf : Measurable f) (α : ℝ) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.borelDiscountedResolvent f α) := by
  intro t
  exact (P.borelDiscountedPast_stronglyAdapted f hf α t).add
    (((P.borelTransitionLaplace_measurable hκ f hf α).comp
      (graphContinuousPath_current_measurable P.geometry t)).stronglyMeasurable.const_mul (Real.exp (-α * (t : ℝ))))

theorem GraphShiftedContactOperatorProblem.borelDiscountedResolvent_condExp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C)
    {α : ℝ} (hα : 0 < α) (t : ℝ≥0) :
    (P.continuousPathLaw hκ x)[P.borelDiscountedFuture f α 0 | graphContinuousNaturalFiltration P.geometry t]
      =ᵐ[P.continuousPathLaw hκ x] P.borelDiscountedResolvent f α t := by
  let inst := P.continuousPathLaw_probability hκ x
  let A := P.borelDiscountedPast f α t
  let V := P.borelDiscountedFuture f α t
  let c := Real.exp (-α * (t : ℝ))
  let m := graphContinuousNaturalFiltration P.geometry t
  have hAi : Integrable A (P.continuousPathLaw hκ x) := P.borelDiscountedPast_integrable hκ x f hf hC0 hC hα.le t
  have hVi : Integrable V (P.continuousPathLaw hκ x) := P.borelDiscountedFuture_integrable hκ x f hf hC hα t
  have hdec : P.borelDiscountedFuture f α 0 =ᵐ[P.continuousPathLaw hκ x] A + c • V :=
    P.borelDiscountedFuture_decomposition hκ x f hf hC hα t
  have hadd := condExp_add hAi (hVi.smul c) m
  have hmul := condExp_smul (μ := P.continuousPathLaw hκ x) c V m
  have hA : (P.continuousPathLaw hκ x)[A | m] =ᵐ[P.continuousPathLaw hκ x] A :=
    EventuallyEq.of_eq (condExp_of_stronglyMeasurable ((graphContinuousNaturalFiltration P.geometry).le t)
      (P.borelDiscountedPast_stronglyAdapted f hf α t) hAi)
  have hV := P.borelDiscountedFuture_condExp hκ x f hf hC0 hC hα t
  filter_upwards [condExp_congr_ae (m := m) hdec, hadd, hmul, hA, hV] with p hd ha hm hpa hpv
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hm
  change (P.continuousPathLaw hκ x)[P.borelDiscountedFuture f α 0 | m] p = A p + c * P.borelTransitionLaplace f α (p t)
  rw [hd, ha, hm, hpa, hpv]

theorem GraphShiftedContactOperatorProblem.borelDiscountedResolvent_martingale
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C)
    {α : ℝ} (hα : 0 < α) :
    Martingale (P.borelDiscountedResolvent f α) (graphContinuousNaturalFiltration P.geometry)
      (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (martingale_condExp (P.borelDiscountedFuture f α 0)
    (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw hκ x)).congr
      (P.borelDiscountedResolvent_stronglyAdapted hκ f hf α)
      (P.borelDiscountedResolvent_condExp hκ x f hf hC0 hC hα)

end TimeTraps.Analysis
