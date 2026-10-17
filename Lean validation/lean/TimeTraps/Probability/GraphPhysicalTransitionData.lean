module

public import TimeTraps.Probability.GraphPhysicalClockMarkov
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! The actual time-changed graph transition on continuous observations.
Measurability, probability bounds, and time continuity precede any
claim about the invariant or reversible physical measure. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.physicalTransitionExpectation
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) (g : GraphRealization P.geometry → ℝ)
    (x : GraphRealization P.geometry) : ℝ :=
  ∫ p, g (p t) ∂P.physicalPathLaw h0 b hb x

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_reference
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) {g : GraphRealization P.geometry → ℝ}
    (hg : Measurable g) (x : GraphRealization P.geometry) :
    P.physicalTransitionExpectation h0 b hb t g x =
      ∫ p, g (P.geometry.physicalPath b hb p t) ∂P.continuousPathLaw h0 x :=
  P.physicalPathKernel_integral h0 b hb x (hg.comp (continuous_eval_const t).measurable)

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_measurable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) {g : GraphRealization P.geometry → ℝ}
    (hg : Measurable g) : Measurable (P.physicalTransitionExpectation h0 b hb t g) :=
  (hg.comp (continuous_eval_const t).measurable).stronglyMeasurable.integral_kernel.measurable

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_bound
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) {g : GraphRealization P.geometry → ℝ}
    {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) (x : GraphRealization P.geometry) :
    ‖P.physicalTransitionExpectation h0 b hb t g x‖ ≤ C := by
  change ‖∫ p, g (p t) ∂P.physicalPathLaw h0 b hb x‖ ≤ C
  have h := norm_integral_le_of_norm_le_const (μ := P.physicalPathLaw h0 b hb x)
    (Eventually.of_forall (fun p => hC (p t)))
  simpa only [probReal_univ, mul_one] using h

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_continuous_time
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (g : C(GraphRealization P.geometry, ℝ))
    (x : GraphRealization P.geometry) :
    Continuous (fun t => P.physicalTransitionExpectation h0 b hb t g x) := by
  apply continuous_of_dominated
    (fun t => (g.continuous.comp (continuous_eval_const t)).measurable.aestronglyMeasurable)
    (fun t => Eventually.of_forall (fun p => g.norm_coe_le_norm (p t)))
    (integrable_const ‖g‖)
    (Eventually.of_forall (fun p => g.continuous.comp p.continuous))

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (g : C(GraphRealization P.geometry, ℝ)) :
    Measurable (fun q : ℝ≥0 × GraphRealization P.geometry =>
      P.physicalTransitionExpectation h0 b hb q.1 g q.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (P.physicalTransitionExpectation_continuous_time h0 b hb g)
    (fun t => P.physicalTransitionExpectation_measurable h0 b hb t g.continuous.measurable)

theorem GraphShiftedContactOperatorProblem.physicalTransitionExpectation_one
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) (x : GraphRealization P.geometry) :
    P.physicalTransitionExpectation h0 b hb t (fun _ => 1) x = 1 := by
  change (∫ _p, (1 : ℝ) ∂P.physicalPathLaw h0 b hb x) = 1
  simp only [integral_const, probReal_univ, one_smul]

end TimeTraps.Analysis
