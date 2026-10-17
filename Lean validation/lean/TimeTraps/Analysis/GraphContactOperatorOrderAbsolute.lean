module

public import TimeTraps.Analysis.GraphContactOperatorFormPhysical
public import TimeTraps.Analysis.IntervalEnergyAbsolute

@[expose] public section

/-! Absolute value of the physical edge representatives preserves vertex
matching and the full network quadratic form. The resulting element lies
in the actual graph H1 Hilbert space, with no separate nodal coordinates.
Both incidences of loops and all parallel edges are retained. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*}

theorem graphContactEnergy_abs (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) :
    GraphEnergy G (fun v => |U v|) (fun e x => |u e x|) := by
  refine ⟨fun e => (hu.edge_energy e).abs, ?_, ?_⟩
  · intro e
    exact congrArg abs (hu.tail_value e)
  · intro e
    exact congrArg abs (hu.head_value e)

variable [Nonempty E]

noncomputable def GraphContactOperatorProblem.operatorOrderAbs (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) : GraphSobolevSpace P.geometry :=
  graphSobolevSpaceOfEnergy P.geometry (graphContactEnergy_abs P.geometry (P.operatorRep_energy u))

theorem GraphContactOperatorProblem.operatorOrderAbs_state_ae (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) (e : E) :
    (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u)) e
      =ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))] fun x => |P.operatorRep u e x| :=
  graphSobolevSpaceOfEnergy_state_ae P.geometry
    (graphContactEnergy_abs P.geometry (P.operatorRep_energy u)) e

theorem GraphContactOperatorProblem.operatorOrderAbs_representative (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) (e : E) :
    EqOn (P.operatorRep (P.operatorOrderAbs u) e) (fun x => |P.operatorRep u e x|)
      (Icc 0 (P.geometry.length e)) :=
  P.operatorRep_ofEnergy (graphContactEnergy_abs P.geometry (P.operatorRep_energy u)) e

theorem GraphContactOperatorProblem.operatorOrderAbs_nodes (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) (v : V) :
    P.operatorNodes (P.operatorOrderAbs u) v = |P.operatorNodes u v| :=
  graphSobolevSpaceOfEnergy_node P.geometry
    (graphContactEnergy_abs P.geometry (P.operatorRep_energy u)) v

variable [Fintype V] [Fintype E]

theorem GraphContactOperatorProblem.operatorForm_orderAbs (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) :
    P.operatorForm (P.operatorOrderAbs u) (P.operatorOrderAbs u) = P.operatorForm u u := by
  change P.operatorForm
    (graphSobolevSpaceOfEnergy P.geometry (graphContactEnergy_abs P.geometry (P.operatorRep_energy u)))
    (graphSobolevSpaceOfEnergy P.geometry (graphContactEnergy_abs P.geometry (P.operatorRep_energy u))) = _
  rw [P.operatorForm_ofEnergy, P.operatorForm_apply]
  unfold graphContactForm
  simp only [mul_assoc, ← pow_two, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [((P.operatorRep_energy u).edge_energy e).abs_derivative_square_ae]
    with x hx
  change P.geometry.conductance e x * deriv (fun y => |P.operatorRep u e y|) x ^ 2 =
    P.geometry.conductance e x * deriv (P.operatorRep u e) x ^ 2
  rw [hx]

end TimeTraps.Analysis
