module

public import TimeTraps.Analysis.GraphShiftedContactHeatSemigroup

@[expose] public section

/-! The actual heat evolution preserves the actual constant-one graph
state when all vertex reactions vanish. This is proved from the original
weak constant-state equation and complete spectral expansion. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.operatorInverse_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) :
    P.operatorInverse (graphSobolevSpaceStateL P.geometry P.operatorOne) =
      graphSobolevSpaceStateL P.geometry P.operatorOne := by
  simpa only [zero_add] using (P.operator_graph_iff _ _).mp (P.operator_one_graph hκ)

theorem GraphShiftedContactOperatorProblem.heatCoefficient_one_inner
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (i : CompactSpectralIndex P.operatorInverse) :
    P.heatCoefficient t i * inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i)
      (graphSobolevSpaceStateL P.geometry P.operatorOne) =
        inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i)
          (graphSobolevSpaceStateL P.geometry P.operatorOne) := by
  by_cases hc : inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i)
      (graphSobolevSpaceStateL P.geometry P.operatorOne) = 0
  · rw [hc, mul_zero]
  · have he := P.operatorCompactPositiveInverse.inner_eigenbasis_apply
      (graphSobolevSpaceStateL P.geometry P.operatorOne) i
    rw [P.operatorInverse_one hκ] at he
    have hi : i.1 = 1 := by
      apply (mul_right_cancel₀ hc)
      simpa only [one_mul] using he.symm
    simp only [heatCoefficient, heatRate, hi, inv_one, sub_self, mul_zero,
      Real.exp_zero, one_mul]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (t : ℝ≥0) :
    P.heatSemigroup t (graphSobolevSpaceStateL P.geometry P.operatorOne) =
      graphSobolevSpaceStateL P.geometry P.operatorOne := by
  apply P.operatorCompactPositiveInverse.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, P.heatSemigroup_inner,
    P.heatCoefficient_one_inner hκ]

theorem GraphShiftedContactOperatorProblem.heatSemigroup_one_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (e : E) :
    (P.heatSemigroup t (graphSobolevSpaceStateL P.geometry P.operatorOne)) e
      =ᵐ[MeasureTheory.volume.restrict (Ioo 0 (P.geometry.length e))] fun _ => 1 := by
  rw [P.heatSemigroup_one hκ]
  exact P.operatorOne_state_ae e

end TimeTraps.Analysis
