module

public import TimeTraps.Probability.GraphBorelResolventDiscountOne
public import TimeTraps.Analysis.GraphHeatResolventBorelContinuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Discounted occupation has continuous paths even for bounded Borel
forcing, by continuity of the Lebesgue primitive. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.borel_path_intervalIntegrable
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C)
    (p : GraphContinuousPath P.geometry) (a b : ℝ) :
    IntervalIntegrable (fun r => f (p r.toNNReal)) volume a b := by
  apply (intervalIntegrable_const (c := C)).mono_fun'
    ((hf.comp (p.continuous.comp continuous_real_toNNReal).measurable).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun r => hC (p r.toNNReal))

omit [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.borelDiscountedPast_continuous
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) (α : ℝ)
    (p : GraphContinuousPath P.geometry) :
    Continuous (fun t => P.borelDiscountedPast f α t p) := by
  have hi (a b : ℝ) : IntervalIntegrable
      (fun r => Real.exp (-α * r) * f (p r.toNNReal)) volume a b :=
    (P.borel_path_intervalIntegrable f hf hC p a b).continuousOn_mul
      (by fun_prop : ContinuousOn (fun r : ℝ => Real.exp (-α * r)) (uIcc a b))
  exact (intervalIntegral.continuous_primitive hi (0 : ℝ)).comp NNReal.continuous_coe

theorem GraphShiftedContactOperatorProblem.borelDiscountedResolventOne_continuous
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C)
    (p : GraphContinuousPath P.geometry) :
    Continuous (fun t => P.borelDiscountedResolventOne f t p) := by
  exact (P.borelDiscountedPast_continuous f hf hC 1 p).add
    ((Real.continuous_exp.comp NNReal.continuous_coe.neg).mul
      ((P.borelResolventOne_continuous hf hC).comp p.continuous))

end TimeTraps.Analysis
