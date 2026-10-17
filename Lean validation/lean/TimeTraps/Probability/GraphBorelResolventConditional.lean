module

public import TimeTraps.Probability.GraphBorelResolventConditionalData

@[expose] public section

/-! Actual conditional discounted continuation for every bounded Borel
graph test. The full raw Markov identity discharges conditional Fubini;
time translation produces the genuine transition Laplace integral. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.borelDiscountedFuture_condExp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C)
    {α : ℝ} (hα : 0 < α) (s : ℝ≥0) :
    (P.continuousPathLaw hκ x)[P.borelDiscountedFuture f α s |
      graphContinuousNaturalFiltration P.geometry s] =ᵐ[P.continuousPathLaw hκ x]
      (fun p => P.borelTransitionLaplace f α (p s)) := by
  let inst := P.continuousPathLaw_probability hκ x
  let ν : Measure ℝ := volume.restrict (Ioi (s : ℝ))
  let F : ℝ × GraphContinuousPath P.geometry → ℝ := fun q =>
    Real.exp (-α * (q.1 - (s : ℝ))) * f (q.2 q.1.toNNReal)
  let G : ℝ × GraphContinuousPath P.geometry → ℝ := fun q =>
    Real.exp (-α * (q.1 - (s : ℝ))) * ∫ z, f z ∂P.realizedTransition (q.1 - (s : ℝ)).toNNReal (q.2 s)
  have hcond : ∀ᵐ r ∂ν,
      (P.continuousPathLaw hκ x)[fun p => F (r, p) | graphContinuousNaturalFiltration P.geometry s]
        =ᵐ[P.continuousPathLaw hκ x] (fun p => G (r, p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := s.coe_nonneg.trans hr.le
    have hsr : s ≤ r.toNNReal := by
      change (s : ℝ) ≤ (r.toNNReal : ℝ)
      rw [Real.coe_toNNReal r hr0]
      exact hr.le
    have hsub : r.toNNReal - s = (r - (s : ℝ)).toNNReal := by
      apply NNReal.eq
      rw [NNReal.coe_sub hsr, Real.coe_toNNReal r hr0,
        Real.coe_toNNReal (r - (s : ℝ)) (sub_nonneg.mpr hr.le)]
    have hc := P.continuousPathLaw_markov_borel hκ x hsr f hf hC0 hC
    have hs := condExp_smul (μ := P.continuousPathLaw hκ x) (Real.exp (-α * (r - (s : ℝ))))
      (fun p : GraphContinuousPath P.geometry => f (p r.toNNReal)) (graphContinuousNaturalFiltration P.geometry s)
    filter_upwards [hc, hs] with p hc hs
    simp only [Pi.smul_apply, smul_eq_mul] at hs
    change _ = Real.exp (-α * (r - (s : ℝ))) * ∫ z, f z ∂P.realizedTransition (r - (s : ℝ)).toNNReal (p s)
    apply hs.trans
    rw [hc, hsub]
  have hc := condExp_integral_sections (ν := ν) (P := P.continuousPathLaw hκ x)
    ((graphContinuousNaturalFiltration P.geometry).le s)
    (P.borelDiscountedFuture_product_integrable hκ x f hf hC hα s)
    (P.borelDiscountedConditional_product_integrable hκ x f hf hC hα s)
    (P.borelDiscountedConditional_jointlyMeasurable hκ f hf α s) hcond
  have hi (p : GraphContinuousPath P.geometry) : (∫ r, G (r, p) ∂ν) = P.borelTransitionLaplace f α (p s) :=
    reflectedDiscounted_shift_integral (s : ℝ) (fun r => Real.exp (-α * r) * ∫ z, f z ∂P.realizedTransition r.toNNReal (p s))
  filter_upwards [hc] with p hp
  exact hp.trans (hi p)

end TimeTraps.Analysis
