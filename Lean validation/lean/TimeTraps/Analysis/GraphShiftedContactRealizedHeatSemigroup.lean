module

public import TimeTraps.Analysis.GraphShiftedContactRealizedHeatComposition
public import TimeTraps.Analysis.GraphShiftedContactRealizedHeatTransition
public import Mathlib.Probability.Kernel.Composition.Comp

@[expose] public section

/-! Exact Chapman--Kolmogorov composition of the genuine graph transition
kernels. The density composition is promoted to equality of Borel measures. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem GraphShiftedContactOperatorProblem.realizedHeatTransition_comp (P : GraphShiftedContactOperatorProblem V E)
    (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    P.realizedHeatTransition t ht ∘ₖ P.realizedHeatTransition s hs =
      P.realizedHeatTransition (s + t) (add_pos hs ht) := by
  ext x A hA
  have hsm := (P.realizedHeatKernel_right_continuous s hs x).measurable.ennreal_ofReal
  have htm := (P.realizedHeatKernel_measurable t ht).ennreal_ofReal
  rw [Kernel.comp_apply' _ _ _ hA, P.realizedHeatTransition_apply s hs x,
    lintegral_withDensity_eq_lintegral_mul _ hsm
      ((P.realizedHeatTransition t ht).measurable_coe hA)]
  calc
    _ = ∫⁻ z, ∫⁻ y in A, ENNReal.ofReal (P.realizedHeatKernel s hs x z) *
        ENNReal.ofReal (P.realizedHeatKernel t ht z y) ∂P.geometry.lengthMeasure
          ∂P.geometry.lengthMeasure := by
      apply lintegral_congr
      intro z
      change ENNReal.ofReal (P.realizedHeatKernel s hs x z) *
        P.realizedHeatTransition t ht z A = _
      rw [P.realizedHeatTransition_apply t ht z, withDensity_apply _ hA]
      exact (lintegral_const_mul _
        (P.realizedHeatKernel_right_continuous t ht z).measurable.ennreal_ofReal).symm
    _ = ∫⁻ y in A, ∫⁻ z, ENNReal.ofReal (P.realizedHeatKernel s hs x z) *
        ENNReal.ofReal (P.realizedHeatKernel t ht z y) ∂P.geometry.lengthMeasure
          ∂P.geometry.lengthMeasure :=
      lintegral_lintegral_swap ((hsm.comp measurable_fst).mul htm).aemeasurable
    _ = ∫⁻ y in A, ENNReal.ofReal (P.realizedHeatKernel (s + t) (add_pos hs ht) x y)
          ∂P.geometry.lengthMeasure := by
      apply lintegral_congr
      intro y
      exact (P.realizedHeatKernel_composition_lintegral s t hs ht x y).symm
    _ = P.realizedHeatTransition (s + t) (add_pos hs ht) x A := by
      rw [P.realizedHeatTransition_apply, withDensity_apply _ hA]

noncomputable def GraphShiftedContactOperatorProblem.realizedTransition (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) : Kernel (GraphRealization P.geometry) (GraphRealization P.geometry) :=
  if ht : 0 < t then P.realizedHeatTransition t ht else Kernel.id

theorem GraphShiftedContactOperatorProblem.realizedTransition_zero (P : GraphShiftedContactOperatorProblem V E) :
    P.realizedTransition 0 = Kernel.id := by simp only [realizedTransition, lt_self_iff_false, dite_false]

theorem GraphShiftedContactOperatorProblem.realizedTransition_pos (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) : P.realizedTransition t = P.realizedHeatTransition t ht := by
  simp only [realizedTransition, dif_pos ht]

theorem GraphShiftedContactOperatorProblem.realizedTransition_mass_le_one (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (x : GraphRealization P.geometry) : P.realizedTransition t x univ ≤ 1 := by
  by_cases ht : 0 < t
  · rw [P.realizedTransition_pos t ht]
    exact P.realizedHeatTransition_mass_le_one t ht x
  · have hz : t = 0 := le_antisymm (le_of_not_gt ht) (show 0 ≤ t from zero_le)
    subst t
    rw [P.realizedTransition_zero]
    simp only [Kernel.id_apply, Measure.dirac_apply_of_mem (mem_univ x), le_refl]

instance GraphShiftedContactOperatorProblem.realizedTransition_finite (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) :
    IsFiniteKernel (P.realizedTransition t) where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, P.realizedTransition_mass_le_one t⟩

theorem GraphShiftedContactOperatorProblem.realizedTransition_add (P : GraphShiftedContactOperatorProblem V E) (s t : ℝ≥0) :
    P.realizedTransition (s + t) = P.realizedTransition t ∘ₖ P.realizedTransition s := by
  by_cases hs : 0 < s
  · by_cases ht : 0 < t
    · rw [P.realizedTransition_pos (s + t) (add_pos hs ht),
        P.realizedTransition_pos s hs, P.realizedTransition_pos t ht]
      exact (P.realizedHeatTransition_comp s t hs ht).symm
    · have hz : t = 0 := le_antisymm (le_of_not_gt ht) (show 0 ≤ t from zero_le)
      subst t
      rw [add_zero, P.realizedTransition_zero, Kernel.id_comp]
  · have hz : s = 0 := le_antisymm (le_of_not_gt hs) (show 0 ≤ s from zero_le)
    subst s
    rw [zero_add, P.realizedTransition_zero, Kernel.comp_id]

end TimeTraps.Analysis
