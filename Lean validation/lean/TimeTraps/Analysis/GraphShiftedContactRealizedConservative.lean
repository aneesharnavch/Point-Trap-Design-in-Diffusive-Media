module

public import TimeTraps.Analysis.GraphShiftedContactRealizedHeatSemigroup

@[expose] public section

/-! When all reactions vanish, the original heat kernel has total mass
one at every point of the compact graph. Its Borel transition is therefore
a genuine Markov kernel without adding a cemetery state. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.heatSobolevL_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (ht : 0 < t) :
    P.heatSobolevL t ht (graphSobolevSpaceStateL P.geometry P.operatorOne) = P.operatorOne := by
  apply graphSobolevSpaceStateL_injective P.geometry
  rw [P.heatSobolevL_state, P.heatSemigroup_one hκ]

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    P.heatPointEvaluation t ht e x (graphSobolevSpaceStateL P.geometry P.operatorOne) = 1 := by
  rw [P.heatPointEvaluation_apply, P.heatSobolevL_one hκ]
  exact P.operatorOne_representative e x.property

theorem GraphShiftedContactOperatorProblem.realizedHeatEvaluation_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry) :
    P.realizedHeatEvaluation t ht x (graphSobolevSpaceStateL P.geometry P.operatorOne) = 1 := by
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  rw [P.realizedHeatEvaluation_edge, P.heatPointEvaluation_one hκ]

theorem GraphShiftedContactOperatorProblem.realizedHeatKernel_mass_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry) :
    (∫ y, P.realizedHeatKernel t ht x y ∂P.geometry.lengthMeasure) = 1 := by
  rw [P.realizedHeatKernel_mass, P.realizedHeatEvaluation_one hκ]

theorem GraphShiftedContactOperatorProblem.realizedHeatTransition_mass_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry) :
    P.realizedHeatTransition t ht x univ = 1 := by
  rw [P.realizedHeatTransition_mass, P.realizedHeatEvaluation_one hκ, ENNReal.ofReal_one]

theorem GraphShiftedContactOperatorProblem.realizedTransition_mass_one
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) (x : GraphRealization P.geometry) :
    P.realizedTransition t x univ = 1 := by
  by_cases ht : 0 < t
  · rw [P.realizedTransition_pos t ht, P.realizedHeatTransition_mass_one hκ]
  · have hz : t = 0 := le_antisymm (le_of_not_gt ht) (show 0 ≤ t from zero_le)
    subst t
    rw [P.realizedTransition_zero]
    exact Measure.dirac_apply_of_mem (mem_univ x)

theorem GraphShiftedContactOperatorProblem.realizedTransition_isMarkov
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (t : ℝ≥0) : IsMarkovKernel (P.realizedTransition t) :=
  ⟨fun x => ⟨P.realizedTransition_mass_one hκ t x⟩⟩

end TimeTraps.Analysis
