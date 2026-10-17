module

public import TimeTraps.Analysis.GraphRobinResolventData

@[expose] public section

/-! The original Robin weak equation rearranged in the conservative
mass-shifted form. The source is the original per-edge rho, and all
vertex terms retain their stated coefficients and signs. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.robinWeak_resolvent_form
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (v : GraphSobolevSpace P.geometry) :
    P.operatorForm (graphSobolevSpaceOfEnergy P.geometry hu.energy) v =
      inner ℝ (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) +
        graphPhysicalSourceL2 P.geometry) (graphSobolevSpaceStateL P.geometry v) -
      ∑ z, κ z * U z * graphRealizedSobolev P.geometry v (P.geometry.vertexPoint z) := by
  have hv := P.operatorRep_energy v
  have hve : graphSobolevSpaceOfEnergy P.geometry hv = v :=
    graphSobolevSpaceOfEnergy_representative_eq P.geometry v
  have hc : P.contactForm (graphSobolevSpaceOfEnergy P.geometry hu.energy) v =
      ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e,
        P.geometry.conductance e x * deriv (u e) x * deriv (P.operatorRep v e) x := by
    have he := P.contactForm_ofEnergy hu.energy hv
    rw [hve] at he
    rw [he]
    simp only [graphContactForm, hP, zero_mul, Finset.sum_const_zero, add_zero]
  have hs : inner ℝ (graphPhysicalSourceL2 P.geometry) (graphSobolevSpaceStateL P.geometry v) =
      ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, P.geometry.source e x * P.operatorRep v e x := by
    have he := P.operatorLoad_physicalSource hv
    rw [hve, P.operatorLoad_apply] at he
    exact he
  have hw := hu.weak_form (P.operatorNodes v) (P.operatorRep v) hv
  rw [P.operatorForm_eq, hc, inner_add_left, hs]
  have hn : (∑ z, κ z * U z * graphRealizedSobolev P.geometry v (P.geometry.vertexPoint z)) =
      ∑ z, κ z * U z * P.operatorNodes v z := by
    simp only [graphRealizedSobolev_vertex, GraphShiftedContactOperatorProblem.operatorNodes]
  rw [hn]
  linarith

theorem GraphShiftedContactOperatorProblem.robinWeak_resolvent_decomposition
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u) :
    graphSobolevSpaceOfEnergy P.geometry hu.energy =
      P.operatorSolution (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) +
        graphPhysicalSourceL2 P.geometry) -
      ∑ z, (κ z * U z) • P.pointResolventSolution (P.geometry.vertexPoint z) := by
  apply eq_sub_iff_add_eq.mpr
  apply (P.operatorSolution_eq_iff _ _).mpr
  intro v
  rw [map_add, add_apply, P.robinWeak_resolvent_form hP hu]
  have he : P.operatorForm (∑ z, (κ z * U z) • P.pointResolventSolution (P.geometry.vertexPoint z)) v =
      ∑ z, κ z * U z * graphRealizedSobolev P.geometry v (P.geometry.vertexPoint z) := by
    change P.operatorForm.flip v (∑ z, (κ z * U z) • P.pointResolventSolution (P.geometry.vertexPoint z)) = _
    simp only [map_sum, map_smul, ContinuousLinearMap.flip_apply,
      P.pointResolventSolution_spec, smul_eq_mul]
  rw [he]
  exact sub_add_cancel _ _

end TimeTraps.Analysis
