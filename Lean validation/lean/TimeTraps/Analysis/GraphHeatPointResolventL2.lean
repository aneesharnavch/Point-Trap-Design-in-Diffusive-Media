module

public import TimeTraps.Analysis.GraphHeatPointResolvent

@[expose] public section

/-! Pointwise source representation for arbitrary edge L2 data. In
particular the source may have unequal edge traces at a vertex. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.realizedSolutionL_pointResolvent_integral
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry)
    (a : GraphRealization P.geometry) :
    P.realizedSolutionL f a = ∑ e, ∫ y in (0 : ℝ)..P.geometry.length e,
      (f e) y * P.pointLocalTimeDiscountedPotential a 1 (P.geometry.edgePointClamped e y) := by
  rw [← P.pointResolventSolution_pairing a f, ← P.operatorLoad_apply,
    P.operatorLoad_representative]
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr_Ioo_of_le (P.geometry.length_pos e).le
  intro y hy
  change (f e) y * P.operatorRep (P.pointResolventSolution a) e y =
    (f e) y * P.pointLocalTimeDiscountedPotential a 1
      (P.geometry.edgePoint e (projIcc 0 (P.geometry.length e) (P.geometry.length_pos e).le y))
  rw [P.pointLocalTimeDiscountedPotential_one_edge,
    projIcc_of_mem (P.geometry.length_pos e).le (Ioo_subset_Icc_self hy)]

theorem GraphShiftedContactOperatorProblem.realizedSolutionL_pointResolvent_weak
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry) :
    GraphShiftedContactL2WeakEquation P f (P.operatorNodes (P.operatorSolution f))
      (P.operatorRep (P.operatorSolution f)) ∧
    (∀ a, graphRealizedSobolev P.geometry (P.operatorSolution f) a =
      ∑ e, ∫ y in (0 : ℝ)..P.geometry.length e,
        (f e) y * P.pointLocalTimeDiscountedPotential a 1 (P.geometry.edgePointClamped e y)) :=
  ⟨P.operatorSolution_physical f, P.realizedSolutionL_pointResolvent_integral f⟩

end TimeTraps.Analysis
