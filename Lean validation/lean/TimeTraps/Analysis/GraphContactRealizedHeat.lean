module

public import TimeTraps.Graph.TopologicalRealizationMeasurable
public import TimeTraps.Analysis.GraphContactHeatEvaluationContinuity

@[expose] public section

/-! Positive-time heat evaluation and Riesz vectors on the genuine compact
graph state space. They descend from the original edge heat operator by
the proved endpoint trace matching, rather than by choosing vertex copies. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Analysis TimeTraps.Graph InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphContactOperatorProblem.realizedHeatEvaluation (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) : GraphRealization P.geometry → (GraphL2Product P.geometry →L[ℝ] ℝ) :=
  P.geometry.realizationTrace (fun e x => P.heatPointEvaluation t ht e x)

theorem GraphContactOperatorProblem.realizedHeatEvaluation_edge (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    P.realizedHeatEvaluation t ht (P.geometry.edgePoint e x) = P.heatPointEvaluation t ht e x :=
  P.geometry.realizationTrace_apply (P.heatNodeEvaluation t ht) _
    (P.heatPointEvaluation_tail t ht) (P.heatPointEvaluation_head t ht) e x

theorem GraphContactOperatorProblem.realizedHeatEvaluation_continuous (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) : Continuous (P.realizedHeatEvaluation t ht) :=
  P.geometry.realizationTrace_continuous (P.heatNodeEvaluation t ht) _
    (P.heatPointEvaluation_continuous t ht)
    (P.heatPointEvaluation_tail t ht) (P.heatPointEvaluation_head t ht)

noncomputable def GraphContactOperatorProblem.realizedHeatVector (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry) : GraphL2Product P.geometry :=
  (toDual ℝ (GraphL2Product P.geometry)).symm (P.realizedHeatEvaluation t ht x)

theorem GraphContactOperatorProblem.realizedHeatVector_edge (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    P.realizedHeatVector t ht (P.geometry.edgePoint e x) = P.heatKernelVector t ht e x := by
  unfold realizedHeatVector heatKernelVector
  rw [P.realizedHeatEvaluation_edge]

theorem GraphContactOperatorProblem.realizedHeatVector_continuous (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) : Continuous (P.realizedHeatVector t ht) :=
  (toDual ℝ (GraphL2Product P.geometry)).symm.continuous.comp
    (P.realizedHeatEvaluation_continuous t ht)

theorem GraphContactOperatorProblem.realizedHeatVector_inner (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry) (f : GraphL2Product P.geometry) :
    inner ℝ (P.realizedHeatVector t ht x) f = P.realizedHeatEvaluation t ht x f :=
  toDual_symm_apply

end TimeTraps.Analysis
