module

public import TimeTraps.Probability.GraphPhysicalClockLaplaceExpectation
public import TimeTraps.Probability.GraphPhysicalClockLaplaceStartData

@[expose] public section

/-! The physical transition Laplace transform equals the named original
reference-clock time integrand. The final exchange is justified by the
proved signed product integrability under every starting law. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_laplace_integrand
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : TimeTraps.Graph.GraphRealization P.geometry)
    {f : TimeTraps.Graph.GraphRealization P.geometry → ℝ} (hf : Measurable f)
    {C q : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (hq : 0 < q) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
      P.physicalTransitionExpectation h0 b hb t.toNNReal f x) =
      ∫ s in Ioi (0 : ℝ), P.physicalClockLaplaceIntegrand h0 b hb q f s x := by
  let inst := P.continuousPathLaw_probability h0 x
  rw [P.physicalTransitionExpectation_laplace_clock h0 b hb x hf hC hq]
  exact (integral_integral_swap (P.physicalClockLaplace_product_integrable h0 b hb x hf hC hq)).symm

end TimeTraps.Analysis
