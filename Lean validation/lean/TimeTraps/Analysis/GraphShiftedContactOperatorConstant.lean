module

public import TimeTraps.Analysis.GraphShiftedContactOperatorUnshifted

@[expose] public section

/-! The actual constant-one graph state lies in the zero eigenspace of
the unshifted operator when every reaction vanishes. Its closed-edge
traces match at every vertex; no positive-contact assumption is used. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*}

theorem graphShiftedEnergy_one (G : MetricGraph V E) :
    GraphEnergy G (fun _ => 1) (fun _ _ => 1) :=
  ⟨fun e => IntervalEnergy.const 1 0 (G.length e), fun _ => rfl, fun _ => rfl⟩

noncomputable def GraphShiftedContactOperatorProblem.operatorOne
    (P : GraphShiftedContactOperatorProblem V E) : GraphSobolevSpace P.geometry :=
  graphSobolevSpaceOfEnergy P.geometry (graphShiftedEnergy_one P.geometry)

theorem GraphShiftedContactOperatorProblem.operatorOne_state_ae
    (P : GraphShiftedContactOperatorProblem V E) (e : E) :
    (graphSobolevSpaceStateL P.geometry P.operatorOne) e
      =ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))] fun _ => 1 :=
  graphSobolevSpaceOfEnergy_state_ae P.geometry (graphShiftedEnergy_one P.geometry) e

variable [Nonempty E]

theorem GraphShiftedContactOperatorProblem.operatorOne_nodes
    (P : GraphShiftedContactOperatorProblem V E) (v : V) : P.operatorNodes P.operatorOne v = 1 :=
  graphSobolevSpaceOfEnergy_node P.geometry (graphShiftedEnergy_one P.geometry) v

variable [Fintype V] [Fintype E]

theorem GraphShiftedContactOperatorProblem.contactForm_one
    (P : GraphShiftedContactOperatorProblem V E) (v : GraphSobolevSpace P.geometry) :
    P.contactForm P.operatorOne v = ∑ a, P.strength a * P.operatorNodes v a := by
  have hv : graphSobolevSpaceOfEnergy P.geometry (P.operatorRep_energy v) = v :=
    graphSobolevSpaceOfEnergy_representative_eq P.geometry v
  change P.contactForm (graphSobolevSpaceOfEnergy P.geometry
    (graphShiftedEnergy_one P.geometry)) v = _
  conv_lhs => rw [← hv]
  rw [P.contactForm_ofEnergy]
  simp only [graphContactForm, deriv_const, zero_mul, mul_zero,
    intervalIntegral.integral_zero, Finset.sum_const_zero, zero_add, mul_one]

theorem GraphShiftedContactOperatorProblem.operator_one_graph
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) :
    (graphSobolevSpaceStateL P.geometry P.operatorOne, 0) ∈ P.operator.graph := by
  apply (P.operator_graph_weak_iff _ _).mpr
  refine ⟨P.operatorOne, rfl, ?_⟩
  intro w
  rw [P.contactForm_one]
  simp only [hκ, zero_mul, Finset.sum_const_zero, inner_zero_left]

end TimeTraps.Analysis
