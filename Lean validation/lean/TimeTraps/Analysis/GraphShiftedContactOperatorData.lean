module

public import TimeTraps.Analysis.GraphShiftedContactCoercivity

@[expose] public section

/-! Independent graph data for the mass-shifted form in ordinary edge
length L2. Reactions are only nonnegative; all of them may vanish. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*}

structure GraphShiftedContactOperatorProblem (V E : Type*) where
  geometry : MetricGraph V E
  strength : V → ℝ
  strength_nonneg : ∀ v, 0 ≤ strength v

noncomputable def GraphShiftedContactOperatorProblem.operatorRep (P : GraphShiftedContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) : E → ℝ → ℝ := graphSobolevRepresentative P.geometry u.val

noncomputable def GraphShiftedContactOperatorProblem.operatorNodes [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) : V → ℝ :=
  graphSobolevNodeValue P.geometry u

noncomputable def GraphShiftedContactOperatorProblem.operatorEdgeL (P : GraphShiftedContactOperatorProblem V E) (e : E) :
    GraphSobolevSpace P.geometry →L[ℝ] IntervalSobolevSpace 0 (P.geometry.length e) :=
  (graphSobolevComponentL P.geometry e).comp (graphSobolevSubspace P.geometry).subtypeL

theorem GraphShiftedContactOperatorProblem.operatorRep_energy [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) :
    GraphEnergy P.geometry (P.operatorNodes u) (P.operatorRep u) := graphSobolevSpace_energy P.geometry u

theorem GraphShiftedContactOperatorProblem.operator_norm_sq [Fintype E]
    (P : GraphShiftedContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) :
    ‖u‖ ^ 2 = (∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, (P.operatorRep u e x) ^ 2) +
      graphDerivativeSquare P.geometry (P.operatorRep u) := by
  change ‖u.val‖ ^ 2 = _
  rw [graphSobolevProduct_norm_sq_integral]
  simp only [intervalH1SizeSq, Finset.sum_add_distrib, graphDerivativeSquare, operatorRep]

end TimeTraps.Analysis
