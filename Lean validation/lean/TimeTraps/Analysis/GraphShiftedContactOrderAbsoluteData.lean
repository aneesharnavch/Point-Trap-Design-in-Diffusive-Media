module

public import TimeTraps.Analysis.GraphShiftedContactOperatorPhysical
public import TimeTraps.Analysis.GraphContactOperatorOrderAbsolute

@[expose] public section

/-! Actual absolute-value graph states for the problem without an anchor.
The full original incidences and ordinary edge mass are retained. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Graph

variable {V E : Type*} [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.operatorOrderAbs (P : GraphShiftedContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) : GraphSobolevSpace P.geometry :=
  graphSobolevSpaceOfEnergy P.geometry (graphContactEnergy_abs P.geometry (P.operatorRep_energy u))

theorem GraphShiftedContactOperatorProblem.operatorOrderAbs_state_ae (P : GraphShiftedContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) (e : E) :
    (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u)) e
      =ᵐ[volume.restrict (Ioo 0 (P.geometry.length e))] fun x => |P.operatorRep u e x| :=
  graphSobolevSpaceOfEnergy_state_ae P.geometry
    (graphContactEnergy_abs P.geometry (P.operatorRep_energy u)) e

theorem GraphShiftedContactOperatorProblem.operatorOrderAbs_representative (P : GraphShiftedContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) (e : E) :
    EqOn (P.operatorRep (P.operatorOrderAbs u) e) (fun x => |P.operatorRep u e x|)
      (Icc 0 (P.geometry.length e)) :=
  P.operatorRep_ofEnergy (graphContactEnergy_abs P.geometry (P.operatorRep_energy u)) e

theorem GraphShiftedContactOperatorProblem.operatorOrderAbs_nodes (P : GraphShiftedContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) (v : V) :
    P.operatorNodes (P.operatorOrderAbs u) v = |P.operatorNodes u v| :=
  graphSobolevSpaceOfEnergy_node P.geometry
    (graphContactEnergy_abs P.geometry (P.operatorRep_energy u)) v

variable [Fintype E]

theorem GraphShiftedContactOperatorProblem.operatorOrderAbs_mass (P : GraphShiftedContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) :
    inner ℝ (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u))
      (graphSobolevSpaceStateL P.geometry (P.operatorOrderAbs u)) =
    inner ℝ (graphSobolevSpaceStateL P.geometry u) (graphSobolevSpaceStateL P.geometry u) := by
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  change ‖graphSobolevStateL P.geometry (P.operatorOrderAbs u).val‖ ^ 2 =
    ‖graphSobolevStateL P.geometry u.val‖ ^ 2
  rw [graphSobolevStateL_norm_sq_integral P.geometry,
    graphSobolevStateL_norm_sq_integral P.geometry]
  change (∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, P.operatorRep (P.operatorOrderAbs u) e x ^ 2) =
    ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, P.operatorRep u e x ^ 2
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_Ioo_of_le (P.geometry.length_pos e).le
  intro x hx
  change P.operatorRep (P.operatorOrderAbs u) e x ^ 2 = P.operatorRep u e x ^ 2
  rw [P.operatorOrderAbs_representative u e (Ioo_subset_Icc_self hx), sq_abs]

end TimeTraps.Analysis
