module

public import TimeTraps.Probability.GraphBorelResolventPast

@[expose] public section

/-! The actual infinite discounted Borel occupation payoff splits into
its literal past occupation and discounted future occupation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.borelDiscountedFuture_decomposition
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) {α : ℝ} (hα : 0 < α) (t : ℝ≥0) :
    P.borelDiscountedFuture f α 0 =ᵐ[P.continuousPathLaw hκ x]
      (fun p => P.borelDiscountedPast f α t p + Real.exp (-α * (t : ℝ)) * P.borelDiscountedFuture f α t p) := by
  let inst := P.continuousPathLaw_probability hκ x
  have hi := P.borelDiscountedFuture_product_integrable hκ x f hf hC hα 0
  simp only [NNReal.coe_zero, sub_zero] at hi
  filter_upwards [hi.prod_left_ae] with p hp
  let g : ℝ → ℝ := fun r => Real.exp (-α * r) * f (p r.toNNReal)
  have hg : IntegrableOn g (Ioi 0) := hp
  have he : Real.exp (-α * (t : ℝ)) * P.borelDiscountedFuture f α t p = ∫ r in Ioi (t : ℝ), g r := by
    unfold borelDiscountedFuture
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro r
    dsimp only [g]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  change (∫ r in Ioi ((0 : ℝ≥0) : ℝ), Real.exp (-α * (r - ((0 : ℝ≥0) : ℝ))) * f (p r.toNNReal)) = _
  simp only [NNReal.coe_zero, sub_zero]
  change (∫ r in Ioi (0 : ℝ), g r) = _
  rw [← intervalIntegral.integral_interval_add_Ioi hg (hg.mono_set (Ioi_subset_Ioi t.coe_nonneg)), ← he]
  rfl

end TimeTraps.Analysis
