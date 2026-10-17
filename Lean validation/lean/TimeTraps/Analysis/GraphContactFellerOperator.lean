module

public import TimeTraps.Analysis.GraphContactFellerData
public import TimeTraps.Analysis.GraphContactRealizedHeatSemigroup

@[expose] public section

/-! The graph transition operators on continuous functions, including
the identity at time zero. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable def GraphContactOperatorProblem.realizedHeatCL
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t) :
    C(GraphRealization P.geometry, ℝ) →L[ℝ] C(GraphRealization P.geometry, ℝ) :=
  LinearMap.mkContinuous
    ({
      toFun := P.realizedHeatC t ht
      map_add' := by
        intro f g
        ext x
        simp only [P.realizedHeatC_apply, ContinuousMap.add_apply]
        exact integral_add (P.realizedHeatC_integrable t ht f x)
          (P.realizedHeatC_integrable t ht g x)
      map_smul' := by
        intro c f
        ext x
        simp only [P.realizedHeatC_apply, ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c f } :
      C(GraphRealization P.geometry, ℝ) →ₗ[ℝ] C(GraphRealization P.geometry, ℝ))
    1 (fun f => by
      change ‖P.realizedHeatC t ht f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using P.realizedHeatC_norm_le t ht f)

theorem GraphContactOperatorProblem.realizedHeatCL_apply
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (f : C(GraphRealization P.geometry, ℝ)) :
    P.realizedHeatCL t ht f = P.realizedHeatC t ht f := rfl

noncomputable def GraphContactOperatorProblem.realizedFeller
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) :
    C(GraphRealization P.geometry, ℝ) →L[ℝ] C(GraphRealization P.geometry, ℝ) :=
  if ht : 0 < t then P.realizedHeatCL t ht else ContinuousLinearMap.id ℝ _

theorem GraphContactOperatorProblem.realizedFeller_zero
    (P : GraphContactOperatorProblem V E) :
    P.realizedFeller 0 = ContinuousLinearMap.id ℝ _ := by
  simp only [realizedFeller, lt_self_iff_false, dite_false]

theorem GraphContactOperatorProblem.realizedFeller_pos
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t) :
    P.realizedFeller t = P.realizedHeatCL t ht := by
  simp only [realizedFeller, dif_pos ht]

theorem GraphContactOperatorProblem.realizedFeller_apply
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0)
    (f : C(GraphRealization P.geometry, ℝ)) (x : GraphRealization P.geometry) :
    P.realizedFeller t f x = ∫ y, f y ∂P.realizedTransition t x := by
  by_cases ht : 0 < t
  · rw [P.realizedFeller_pos t ht, P.realizedHeatCL_apply, P.realizedHeatC_apply,
      P.realizedTransition_pos t ht]
  · have hz : t = 0 := le_antisymm (le_of_not_gt ht) (show 0 ≤ t from zero_le)
    subst t
    simp only [P.realizedFeller_zero, ContinuousLinearMap.id_apply,
      P.realizedTransition_zero, Kernel.id_apply, integral_dirac]

theorem GraphContactOperatorProblem.realizedFeller_norm_le
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0)
    (f : C(GraphRealization P.geometry, ℝ)) : ‖P.realizedFeller t f‖ ≤ ‖f‖ := by
  by_cases ht : 0 < t
  · rw [P.realizedFeller_pos t ht, P.realizedHeatCL_apply]
    exact P.realizedHeatC_norm_le t ht f
  · have hz : t = 0 := le_antisymm (le_of_not_gt ht) (show 0 ≤ t from zero_le)
    subst t
    simp only [P.realizedFeller_zero, ContinuousLinearMap.id_apply, le_refl]

theorem GraphContactOperatorProblem.realizedFeller_nonneg
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0)
    (f : C(GraphRealization P.geometry, ℝ)) (hf : ∀ y, 0 ≤ f y)
    (x : GraphRealization P.geometry) : 0 ≤ P.realizedFeller t f x := by
  rw [P.realizedFeller_apply]
  exact integral_nonneg hf

end TimeTraps.Analysis
