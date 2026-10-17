module

public import TimeTraps.Analysis.GraphShiftedContactHeatGenerator
public import TimeTraps.Analysis.ShiftedInverseHeatGenerator

@[expose] public section

/-! Every initial edge L2 state enters the original graph operator domain
at positive time and satisfies the full original weak diffusion equation.
The ordinary mass used to construct the inverse cancels from this equation. -/

namespace TimeTraps.Analysis

open Set

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.operator_eq_translated
    (P : GraphShiftedContactOperatorProblem V E) :
    P.operator = translatedInverseOperator P.operatorInverse P.operatorInverse_injective 1 := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [P.operator_graph_iff, translatedInverseOperator_graph_iff, one_smul]

theorem GraphShiftedContactOperatorProblem.heatCurve_eq_translated
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry) :
    P.heatCurve x = P.operatorCompactPositiveInverse.translatedHeatCurve 1 x := by
  funext t
  simp only [heatCurve, CompactPositiveInverse.translatedHeatCurve, one_mul]

theorem GraphShiftedContactOperatorProblem.heatCurve_mem_domain_of_pos
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry)
    {t : ℝ} (ht : 0 < t) : P.heatCurve x t ∈ P.operator.domain := by
  rw [P.operator_eq_translated, P.heatCurve_eq_translated]
  exact P.operatorCompactPositiveInverse.translatedHeatCurve_mem_domain_of_pos 1 x ht

set_option backward.isDefEq.respectTransparency false in
theorem GraphShiftedContactOperatorProblem.heatCurve_hasDerivAt_of_pos
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry)
    {t : ℝ} (ht : 0 < t) : HasDerivAt (P.heatCurve x)
      (-P.operator ⟨P.heatCurve x t, P.heatCurve_mem_domain_of_pos x ht⟩) t := by
  change HasDerivAt (P.heatCurve x)
    (-(inverseOperator P.operatorInverse P.operatorInverse_injective
      ⟨P.heatCurve x t, P.heatCurve_mem_domain_of_pos x ht⟩ - P.heatCurve x t)) t
  have hd := P.operatorCompactPositiveInverse.translatedHeatCurve_hasDerivAt 1 x ht
  have hg := hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => congrFun (P.heatCurve_eq_translated x) s))
  simpa only [heatCurve, CompactPositiveInverse.translatedHeatCurve, one_mul,
    translatedInverseOperator_apply, one_smul] using hg

theorem GraphShiftedContactOperatorProblem.heatCurve_deriv_graph_of_pos
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry)
    {t : ℝ} (ht : 0 < t) :
    (P.heatCurve x t, -deriv (P.heatCurve x) t) ∈ P.operator.graph := by
  rw [P.operator_eq_translated, P.heatCurve_eq_translated]
  exact P.operatorCompactPositiveInverse.translatedHeatCurve_deriv_graph 1 x ht

theorem GraphShiftedContactOperatorProblem.heatCurve_physical_of_pos
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphL2Product P.geometry)
    {t : ℝ} (ht : 0 < t) :
    ∃ (U : V → ℝ) (u : E → ℝ → ℝ) (hu : TimeTraps.Graph.GraphEnergy P.geometry U u),
      graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu) = P.heatCurve x t ∧
        ∀ (W : V → ℝ) (w : E → ℝ → ℝ), TimeTraps.Graph.GraphEnergy P.geometry W w →
          graphContactForm P.geometry P.strength U W u w =
            ∑ e, ∫ z in (0 : ℝ)..P.geometry.length e, ((-deriv (P.heatCurve x) t) e) z * w e z :=
  (P.operator_graph_physical_iff _ _).mp (P.heatCurve_deriv_graph_of_pos x ht)

end TimeTraps.Analysis
