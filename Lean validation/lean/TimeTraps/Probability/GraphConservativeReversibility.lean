module

public import TimeTraps.Analysis.GraphShiftedContactRealizedConservative
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Detailed balance of the actual original graph transition follows
from its symmetric length density. Zero time is the genuine identity
kernel. In the conservative case this yields invariance of graph length. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.realizedHeatTransition_reversible
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t) :
    Kernel.IsReversible (P.realizedHeatTransition t ht) P.geometry.lengthMeasure := by
  intro A B hA hB
  calc
    _ = ∫⁻ x in A, ∫⁻ y in B, ENNReal.ofReal (P.realizedHeatKernel t ht x y)
        ∂P.geometry.lengthMeasure ∂P.geometry.lengthMeasure := by
      apply lintegral_congr
      intro x
      rw [P.realizedHeatTransition_apply, withDensity_apply _ hB]
    _ = ∫⁻ y in B, ∫⁻ x in A, ENNReal.ofReal (P.realizedHeatKernel t ht x y)
        ∂P.geometry.lengthMeasure ∂P.geometry.lengthMeasure :=
      lintegral_lintegral_swap (P.realizedHeatKernel_measurable t ht).ennreal_ofReal.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      rw [P.realizedHeatTransition_apply, withDensity_apply _ hA]
      apply lintegral_congr
      intro x
      exact congrArg ENNReal.ofReal (P.realizedHeatKernel_symmetric t ht x y)

theorem GraphShiftedContactOperatorProblem.realizedTransition_reversible
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) :
    Kernel.IsReversible (P.realizedTransition t) P.geometry.lengthMeasure := by
  by_cases ht : 0 < t
  · rw [P.realizedTransition_pos t ht]
    exact P.realizedHeatTransition_reversible t ht
  · have hz : t = 0 := le_antisymm (le_of_not_gt ht) (show 0 ≤ t from zero_le)
    subst t
    rw [P.realizedTransition_zero]
    intro A B hA hB
    simp_rw [Kernel.id_apply, Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hB]
    rw [lintegral_indicator_one hB, lintegral_indicator_one hA,
      Measure.restrict_apply hB, Measure.restrict_apply hA, inter_comm]

theorem GraphShiftedContactOperatorProblem.realizedTransition_length_invariant
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0) (t : ℝ≥0) :
    Kernel.Invariant (P.realizedTransition t) P.geometry.lengthMeasure := by
  let inst := P.realizedTransition_isMarkov h0 t
  exact (P.realizedTransition_reversible t).invariant

end TimeTraps.Analysis
