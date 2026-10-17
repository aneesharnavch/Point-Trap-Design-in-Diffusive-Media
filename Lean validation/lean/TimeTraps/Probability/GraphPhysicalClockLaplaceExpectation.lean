module

public import TimeTraps.Probability.GraphPhysicalClockLaplaceIntegrable

@[expose] public section

/-! The actual physical-time transition Laplace transform equals the
reference-path expectation with the original speed clock and speed
factor. All signed Fubini operations have genuine product integrability. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_laplace_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    {f : GraphRealization P.geometry → ℝ} (hf : Measurable f)
    {C q : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (hq : 0 < q) :
    IntegrableOn (fun t : ℝ => Real.exp (-q * t) *
      P.physicalTransitionExpectation h0 b hb t.toNNReal f x) (Ioi 0) := by
  let inst := P.continuousPathLaw_probability h0 x
  have hh := (P.physicalPathLaplace_product_integrable h0 b hb x hf hC hq).integral_prod_left
  apply hh.congr
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [integral_const_mul, ← P.physicalTransitionExpectation_reference h0 b hb t.toNNReal hf x]

theorem GraphShiftedContactOperatorProblem.physicalClockLaplace_integral_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    {f : GraphRealization P.geometry → ℝ} (hf : Measurable f)
    {C q : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (hq : 0 < q) :
    Integrable (fun p => ∫ s in Ioi (0 : ℝ),
      Real.exp (-q * (P.geometry.physicalClock b hb s.toNNReal p : ℝ)) *
        f (p s.toNNReal) * P.geometry.physicalSpeed b (p s.toNNReal))
      (P.continuousPathLaw h0 x) := by
  let inst := P.continuousPathLaw_probability h0 x
  exact (P.physicalClockLaplace_product_integrable h0 b hb x hf hC hq).integral_prod_right

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_laplace_clock
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    {f : GraphRealization P.geometry → ℝ} (hf : Measurable f)
    {C q : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (hq : 0 < q) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
      P.physicalTransitionExpectation h0 b hb t.toNNReal f x) =
      ∫ p, (∫ s in Ioi (0 : ℝ),
        Real.exp (-q * (P.geometry.physicalClock b hb s.toNNReal p : ℝ)) *
          f (p s.toNNReal) * P.geometry.physicalSpeed b (p s.toNNReal))
        ∂P.continuousPathLaw h0 x := by
  let inst := P.continuousPathLaw_probability h0 x
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ p,
        Real.exp (-q * t) * f (P.geometry.physicalPath b hb p t.toNNReal)
          ∂P.continuousPathLaw h0 x := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      dsimp only
      rw [integral_const_mul, P.physicalTransitionExpectation_reference h0 b hb t.toNNReal hf x]
    _ = ∫ p, (∫ t in Ioi (0 : ℝ),
        Real.exp (-q * t) * f (P.geometry.physicalPath b hb p t.toNNReal))
          ∂P.continuousPathLaw h0 x :=
      integral_integral_swap (P.physicalPathLaplace_product_integrable h0 b hb x hf hC hq)
    _ = _ := integral_congr_ae (Eventually.of_forall (fun p => P.geometry.physicalClock_laplace_path b hb p f q))

end TimeTraps.Analysis
