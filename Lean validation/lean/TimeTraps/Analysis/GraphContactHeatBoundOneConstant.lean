module

public import TimeTraps.Analysis.GraphContactOperatorOrderLoad

@[expose] public section

/-! The constant one function is an actual graph H1 state. Its edge
derivatives vanish, while all vertex contact terms remain in its form
pairing. No operator-domain premise is imposed on this supersolution. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*}

theorem graphContactEnergy_one (G : MetricGraph V E) :
    GraphEnergy G (fun _ => 1) (fun _ _ => 1) :=
  ⟨fun e => IntervalEnergy.const 1 0 (G.length e), fun _ => rfl, fun _ => rfl⟩

noncomputable def GraphContactOperatorProblem.operatorOne (P : GraphContactOperatorProblem V E) :
    GraphSobolevSpace P.geometry :=
  graphSobolevSpaceOfEnergy P.geometry (graphContactEnergy_one P.geometry)

theorem GraphContactOperatorProblem.operatorOne_representative (P : GraphContactOperatorProblem V E) (e : E) :
    EqOn (P.operatorRep P.operatorOne e) (fun _ => 1) (Icc 0 (P.geometry.length e)) :=
  P.operatorRep_ofEnergy (graphContactEnergy_one P.geometry) e

theorem GraphContactOperatorProblem.operatorOne_state_ae (P : GraphContactOperatorProblem V E) (e : E) :
    (graphSobolevSpaceStateL P.geometry P.operatorOne) e
      =ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))] fun _ => 1 :=
  graphSobolevSpaceOfEnergy_state_ae P.geometry (graphContactEnergy_one P.geometry) e

variable [Nonempty E]

theorem GraphContactOperatorProblem.operatorOne_nodes (P : GraphContactOperatorProblem V E) (v : V) :
    P.operatorNodes P.operatorOne v = 1 :=
  graphSobolevSpaceOfEnergy_node P.geometry (graphContactEnergy_one P.geometry) v

variable [Fintype V] [Fintype E]

theorem GraphContactOperatorProblem.operatorForm_one (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) :
    P.operatorForm P.operatorOne u = ∑ v, P.strength v * P.operatorNodes u v := by
  have hu : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy u) = u :=
    graphSobolevSpaceOfEnergy_representative_eq P.geometry u
  change P.operatorForm (graphSobolevSpaceOfEnergy P.geometry
    (graphContactEnergy_one P.geometry)) u = _
  conv_lhs => rw [← hu]
  rw [P.operatorForm_ofEnergy]
  simp only [deriv_const, zero_mul, intervalIntegral.integral_zero, Finset.sum_const_zero,
    mul_zero, zero_add, mul_one]

end TimeTraps.Analysis
