module

public import TimeTraps.Analysis.GraphShiftedContactHeatBoundOne
public import TimeTraps.Analysis.CompactHeatInverseComposition

@[expose] public section

/-! Actual positive-time network heat evolution as a bounded map into
the original vertex-continuous H1 space. Every closed-edge point and every
vertex can therefore be evaluated continuously from arbitrary L2 data. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

noncomputable def GraphShiftedContactOperatorProblem.heatSobolevL (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) : GraphL2Product P.geometry →L[ℝ] GraphSobolevSpace P.geometry :=
  Real.exp (t : ℝ) • P.operatorSolution.comp (P.operatorCompactPositiveInverse.heatInverseL t ht)

theorem GraphShiftedContactOperatorProblem.heatSobolevL_state (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (f : GraphL2Product P.geometry) :
    graphSobolevSpaceStateL P.geometry (P.heatSobolevL t ht f) = P.heatSemigroup t f := by
  change graphSobolevSpaceStateL P.geometry
      (Real.exp (t : ℝ) • P.operatorSolution (P.operatorCompactPositiveInverse.heatInverseL t ht f)) =
    Real.exp (t : ℝ) • P.operatorCompactPositiveInverse.heatSemigroup t f
  rw [map_smul]
  congr 1
  exact P.operatorCompactPositiveInverse.heatInverseL_right_inverse t ht f

theorem GraphShiftedContactOperatorProblem.heatSobolevL_state_ae (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (f : GraphL2Product P.geometry) (e : E) :
    (P.heatSemigroup t f) e =ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))]
      P.operatorRep (P.heatSobolevL t ht f) e := by
  rw [← P.heatSobolevL_state t ht f]
  exact graphSobolevRepresentative_state_ae P.geometry (P.heatSobolevL t ht f).val e

theorem GraphShiftedContactOperatorProblem.heatSobolevL_add (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (f : GraphL2Product P.geometry) :
    P.heatSobolevL (s + t) (lt_add_of_lt_of_nonneg hs (show 0 ≤ t from zero_le)) f =
      P.heatSobolevL s hs (P.heatSemigroup t f) := by
  apply graphSobolevSpaceStateL_injective P.geometry
  rw [P.heatSobolevL_state, P.heatSobolevL_state, P.heatSemigroup_add]
  rfl

noncomputable def GraphShiftedContactOperatorProblem.heatPointEvaluation (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    GraphL2Product P.geometry →L[ℝ] ℝ :=
  ((evalL (P.geometry.length_pos e) x x.property).comp (P.operatorEdgeL e)).comp (P.heatSobolevL t ht)

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_apply (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (f : GraphL2Product P.geometry) :
    P.heatPointEvaluation t ht e x f = P.operatorRep (P.heatSobolevL t ht f) e x := rfl

noncomputable def GraphShiftedContactOperatorProblem.heatNodeEvaluation (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (v : V) : GraphL2Product P.geometry →L[ℝ] ℝ :=
  (graphSobolevNodeValueL P.geometry v).comp (P.heatSobolevL t ht)

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_tail (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    P.heatPointEvaluation t ht e ⟨0, le_rfl, (P.geometry.length_pos e).le⟩ =
      P.heatNodeEvaluation t ht (P.geometry.tail e) := by
  ext f
  exact (graphSobolevNodeValue_tail P.geometry (P.heatSobolevL t ht f) e).symm

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_head (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    P.heatPointEvaluation t ht e ⟨P.geometry.length e, (P.geometry.length_pos e).le, le_rfl⟩ =
      P.heatNodeEvaluation t ht (P.geometry.head e) := by
  ext f
  exact (graphSobolevNodeValue_head P.geometry (P.heatSobolevL t ht f) e).symm

end TimeTraps.Analysis
