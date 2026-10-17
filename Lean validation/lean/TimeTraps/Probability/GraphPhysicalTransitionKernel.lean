module

public import TimeTraps.Probability.GraphPhysicalTransitionData

@[expose] public section

/-! The physical state transition is the evaluation marginal of the
already constructed physical path kernel. Probability and compatibility
with the actual expectation are derived before any reversibility claim. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.physicalTransition
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) :
    Kernel (GraphRealization P.geometry) (GraphRealization P.geometry) :=
  (P.physicalPathKernel h0 b hb).map (fun p => p t)

instance GraphShiftedContactOperatorProblem.physicalTransition_isMarkov
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) :
    IsMarkovKernel (P.physicalTransition h0 b hb t) := by
  unfold physicalTransition
  exact Kernel.IsMarkovKernel.map _ (continuous_eval_const t).measurable

theorem GraphShiftedContactOperatorProblem.physicalTransition_apply
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) (x : GraphRealization P.geometry) :
    P.physicalTransition h0 b hb t x = (P.physicalPathLaw h0 b hb x).map (fun p => p t) :=
  Kernel.map_apply _ (continuous_eval_const t).measurable x

theorem GraphShiftedContactOperatorProblem.physicalTransition_integral
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (t : ℝ≥0) (x : GraphRealization P.geometry)
    {g : GraphRealization P.geometry → ℝ} (hg : Measurable g) :
    (∫ y, g y ∂P.physicalTransition h0 b hb t x) =
      P.physicalTransitionExpectation h0 b hb t g x := by
  rw [P.physicalTransition_apply]
  exact integral_map (continuous_eval_const t).measurable.aemeasurable hg.aestronglyMeasurable

theorem GraphShiftedContactOperatorProblem.physicalTransition_zero
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) : P.physicalTransition h0 b hb 0 = Kernel.id := by
  ext x s hs
  rw [P.physicalTransition_apply]
  have hm : (P.physicalPathLaw h0 b hb x).map (fun p => p 0) =
      (P.physicalPathLaw h0 b hb x).map (fun _ => x) :=
    Measure.map_congr (P.physicalPathLaw_initial h0 b hb x)
  rw [hm, Measure.map_const]
  simp only [measure_univ, one_smul, Kernel.id_apply]

theorem GraphShiftedContactOperatorProblem.physicalTransition_vertex_value_independent
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (t : ℝ≥0) :
    P.physicalTransition h0 b hb t = P.physicalTransition h0 c hc t := by
  ext x s hs
  rw [P.physicalTransition_apply, P.physicalTransition_apply,
    P.physicalPathLaw_vertex_value_independent h0 b c hb hc x]

end TimeTraps.Analysis
