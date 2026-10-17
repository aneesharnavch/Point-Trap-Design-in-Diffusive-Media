module

public import TimeTraps.Analysis.GraphContactOperatorData
public import TimeTraps.Analysis.GraphContactOperatorMultiplier

@[expose] public section

/-! The actual bounded variable-conductance/contact bilinear operator on
full graph H1. Its formula is exactly the original edge integrals and
vertex reactions, with no replacement of the weak-test space. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphContactOperatorProblem.operatorForm (P : GraphContactOperatorProblem V E) :
    GraphSobolevSpace P.geometry →L[ℝ] GraphSobolevSpace P.geometry →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (GraphSobolevSpace P.geometry) :=
    Submodule.seminormedAddCommGroup (graphSobolevSubspace P.geometry)
  letI : NormedSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.normedSpace (graphSobolevSubspace P.geometry)
  let B : E → (GraphSobolevSpace P.geometry →L[ℝ] GraphSobolevSpace P.geometry →L[ℝ] ℝ) :=
    fun e => (innerSL ℝ).bilinearComp
    ((graphContactOperatorMultiplyL P.geometry e).comp
      ((gradientL 0 (P.geometry.length e)).comp (P.operatorEdgeL e)))
    ((gradientL 0 (P.geometry.length e)).comp (P.operatorEdgeL e))
  exact (∑ e, B e) +
    ∑ v, P.strength v • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (graphSobolevNodeValueL P.geometry v) (graphSobolevNodeValueL P.geometry v)

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem GraphContactOperatorProblem.operator_gradient_pairing
    (P : GraphContactOperatorProblem V E) (u w : GraphSobolevSpace P.geometry) (e : E) :
    inner ℝ (graphContactOperatorMultiplyL P.geometry e (u.val e).gradient) (w.val e).gradient =
      ∫ x in (0 : ℝ)..P.geometry.length e,
        P.geometry.conductance e x * deriv (P.operatorRep u e) x * deriv (P.operatorRep w e) x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le (P.geometry.length_pos e).le,
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [graphContactOperatorMultiplyL_coe P.geometry e (u.val e).gradient,
    ((u.val e).representative_spec (P.geometry.length_pos e)).2.2,
    ((w.val e).representative_spec (P.geometry.length_pos e)).2.2] with x hM hu hw
  simp only [Real.inner_apply, hM, hu, hw]
  rfl

theorem GraphContactOperatorProblem.operatorForm_apply (P : GraphContactOperatorProblem V E)
    (u w : GraphSobolevSpace P.geometry) :
    P.operatorForm u w = graphContactForm P.geometry P.strength
      (P.operatorNodes u) (P.operatorNodes w) (P.operatorRep u) (P.operatorRep w) := by
  simp only [operatorForm, add_apply, smul_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul, ContinuousLinearMap.comp_apply]
  change (∑ e, inner ℝ (graphContactOperatorMultiplyL P.geometry e (u.val e).gradient)
    (w.val e).gradient) + ∑ v, P.strength v * (P.operatorNodes u v * P.operatorNodes w v) = _
  simp only [P.operator_gradient_pairing, graphContactForm, mul_assoc]

theorem GraphContactOperatorProblem.operatorForm_symmetric (P : GraphContactOperatorProblem V E)
    (u w : GraphSobolevSpace P.geometry) : P.operatorForm u w = P.operatorForm w u := by
  rw [P.operatorForm_apply, P.operatorForm_apply]
  unfold graphContactForm
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr
    intro x _
    ring
  · apply Finset.sum_congr rfl
    intro v _
    ring

theorem GraphContactOperatorProblem.operatorForm_nonneg (P : GraphContactOperatorProblem V E)
    (u : GraphSobolevSpace P.geometry) : 0 ≤ P.operatorForm u u := by
  rw [P.operatorForm_apply]
  exact graphContactForm_nonneg P.geometry P.strength _ P.strength_nonneg _

theorem GraphContactOperatorProblem.operatorForm_coercive (P : GraphContactOperatorProblem V E) :
    @IsCoercive (GraphSobolevSpace P.geometry)
      (Submodule.seminormedAddCommGroup (graphSobolevSubspace P.geometry))
      (Submodule.normedSpace (graphSobolevSubspace P.geometry)) P.operatorForm := by
  obtain ⟨c, hc, hb⟩ := graphContactForm_norm_coercive P.geometry P.strength
    P.strength_nonneg P.strength_anchor
  refine ⟨c, hc, ?_⟩
  intro u
  have h := hb u
  change c * ‖u‖ ^ 2 ≤ graphContactForm P.geometry P.strength
    (P.operatorNodes u) (P.operatorNodes u) (P.operatorRep u) (P.operatorRep u) at h
  rw [← P.operatorForm_apply u u] at h
  simpa only [pow_two, mul_assoc] using h

end TimeTraps.Analysis
