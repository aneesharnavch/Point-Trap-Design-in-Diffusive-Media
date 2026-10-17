module

public import TimeTraps.Probability.GraphBorelResolventMartingale
public import TimeTraps.Probability.GraphBorelResolventKernel

@[expose] public section

/-! The discounted bounded-Borel martingale now uses the independently
constructed original graph weak resolvent, with no analytic identification
left as a premise. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.borelDiscountedResolventOne
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  P.borelDiscountedPast f 1 t p + Real.exp (-(t : ℝ)) * P.borelResolventOne f (p t)

theorem GraphShiftedContactOperatorProblem.borelDiscountedResolventOne_eq
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) :
    P.borelDiscountedResolventOne f = P.borelDiscountedResolvent f 1 := by
  funext t p
  simp only [borelDiscountedResolventOne, borelDiscountedResolvent, neg_one_mul,
    P.borelTransitionLaplace_one_eq (p t) f hf hC]

theorem GraphShiftedContactOperatorProblem.borelDiscountedResolventOne_martingale
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C) :
    Martingale (P.borelDiscountedResolventOne f) (graphContinuousNaturalFiltration P.geometry)
      (P.continuousPathLaw hκ x) := by
  rw [P.borelDiscountedResolventOne_eq f hf hC]
  exact P.borelDiscountedResolvent_martingale hκ x f hf hC0 hC (α := 1) (by norm_num)

end TimeTraps.Analysis
