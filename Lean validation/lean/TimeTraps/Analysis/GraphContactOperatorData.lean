module

public import TimeTraps.Analysis.GraphContactCoercivity

@[expose] public section

/-! Data for the original variable-conductance contact operator in ordinary
edge-length L2. Nonnegative reactions and one positive reaction allow
passive vertices. A speed-density weighted generator is not defined here. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*}

structure GraphContactOperatorProblem (V E : Type*) where
  geometry : MetricGraph V E
  strength : V → ℝ
  strength_nonneg : ∀ v, 0 ≤ strength v
  strength_anchor : ∃ v, 0 < strength v

noncomputable def GraphContactOperatorProblem.operatorRep (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) : E → ℝ → ℝ := graphSobolevRepresentative P.geometry u.val

noncomputable def GraphContactOperatorProblem.operatorNodes [Nonempty E]
    (P : GraphContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) : V → ℝ :=
  graphSobolevNodeValue P.geometry u

noncomputable def GraphContactOperatorProblem.operatorEdgeL (P : GraphContactOperatorProblem V E) (e : E) :
    GraphSobolevSpace P.geometry →L[ℝ] IntervalSobolevSpace 0 (P.geometry.length e) :=
  (graphSobolevComponentL P.geometry e).comp (graphSobolevSubspace P.geometry).subtypeL

theorem GraphContactOperatorProblem.operatorRep_energy [Nonempty E]
    (P : GraphContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) :
    GraphEnergy P.geometry (P.operatorNodes u) (P.operatorRep u) := graphSobolevSpace_energy P.geometry u

theorem GraphContactOperatorProblem.operator_norm_sq [Fintype E]
    (P : GraphContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) :
    ‖u‖ ^ 2 = (∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, (P.operatorRep u e x) ^ 2) +
      graphDerivativeSquare P.geometry (P.operatorRep u) := by
  change ‖u.val‖ ^ 2 = _
  rw [graphSobolevProduct_norm_sq_integral]
  simp only [intervalH1SizeSq, Finset.sum_add_distrib, graphDerivativeSquare, operatorRep]

end TimeTraps.Analysis
