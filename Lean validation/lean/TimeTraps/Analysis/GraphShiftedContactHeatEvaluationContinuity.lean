module

public import TimeTraps.Analysis.GraphShiftedContactHeatKernelVector
public import TimeTraps.Analysis.IntervalSobolevEvaluationContinuity

@[expose] public section

/-! Norm-continuity of positive-time edge evaluation and its Riesz vector.
The actual graph H1 map supplies the uniform evaluation modulus, with
variable conductance and passive vertices retained. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Analysis TimeTraps.Graph InnerProductSpace IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance shiftedIntervalKernelNormedSpace (l r : ℝ) :
    NormedSpace ℝ (IntervalSobolevSpace l r) := Submodule.normedSpace (intervalSobolevGraph l r)

noncomputable local instance shiftedGraphKernelNormedSpace (G : MetricGraph V E) :
    NormedSpace ℝ (GraphSobolevSpace G) := Submodule.normedSpace (graphSobolevSubspace G)

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_continuous (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    Continuous (fun x : Icc (0 : ℝ) (P.geometry.length e) => P.heatPointEvaluation t ht e x) :=
  ((evalL_continuous (P.geometry.length_pos e)).clm_comp_const (P.operatorEdgeL e)).clm_comp_const
    (P.heatSobolevL t ht)

theorem GraphShiftedContactOperatorProblem.heatKernelVector_continuous (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    Continuous (fun x : Icc (0 : ℝ) (P.geometry.length e) => P.heatKernelVector t ht e x) :=
  (toDual ℝ (GraphL2Product P.geometry)).symm.continuous.comp
    (P.heatPointEvaluation_continuous t ht e)

end TimeTraps.Analysis
