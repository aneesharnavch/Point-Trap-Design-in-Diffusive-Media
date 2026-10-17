module

public import TimeTraps.Probability.BrownianIntegralTruncationDomain
public import TimeTraps.Probability.BrownianIntegralConditionalPast

@[expose] public section

/-! Time truncation lies in the closed past subspace; the discarded tail
lies in the closed future subspace. Both are statements about the actual
product-L² integrand, proved by continuity from elementary generators. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem brownianIntegralSpace_mem_of_generators
    (S : Submodule ℝ (brownianIntegralSpace B hBm P))
    (hS : IsClosed (S : Set (brownianIntegralSpace B hBm P)))
    (hgen : ∀ a, brownianIntegralGenerator a ∈ S) (f : brownianIntegralSpace B hBm P) : f ∈ S := by
  let x := fun a : BrownianIntegralElementary B hBm P => a.processL2
  refine (TimeTraps.Analysis.gramClosureInclusion_dense x).induction_on f hS ?_
  intro v
  have hs : ∀ w (hw : w ∈ Submodule.span ℝ (range x)),
      TimeTraps.Analysis.gramClosureInclusion x ⟨w, hw⟩ ∈ S := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, rfl⟩ := hw
      exact hgen a
    | zero =>
      change TimeTraps.Analysis.gramClosureInclusion x 0 ∈ S
      rw [map_zero]
      exact S.zero_mem
    | add w z hw hz ihw ihz =>
      change TimeTraps.Analysis.gramClosureInclusion x (⟨w, hw⟩ + ⟨z, hz⟩) ∈ S
      rw [map_add]
      exact S.add_mem ihw ihz
    | smul c w hw ih =>
      change TimeTraps.Analysis.gramClosureInclusion x (c • ⟨w, hw⟩) ∈ S
      rw [map_smul]
      exact S.smul_mem c ih
  exact hs v v.property

theorem brownianTimeCutoff_mem_past (t : ℝ≥0) (f : brownianIntegralSpace B hBm P) :
    brownianTimeCutoff B hBm P t f ∈ brownianIntegralPastSpace B hBm P t := by
  let S := (brownianIntegralPastSpace B hBm P t).comap (brownianTimeCutoff B hBm P t).toLinearMap
  have hS : IsClosed (S : Set (brownianIntegralSpace B hBm P)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (brownianTimeCutoff B hBm P t).continuous
  apply brownianIntegralSpace_mem_of_generators S hS _ f
  intro a
  change brownianTimeCutoff B hBm P t (brownianIntegralGenerator a) ∈
    brownianIntegralPastSpace B hBm P t
  by_cases ht : a.left ≤ t
  · rw [brownianTimeCutoff_generator a ht]
    exact brownianIntegralGenerator_mem_past _ (min_le_right a.right t)
  · rw [brownianTimeCutoff_generator_zero a (le_of_not_ge ht)]
    exact (brownianIntegralPastSpace B hBm P t).zero_mem

theorem brownianTimeCutoff_sub_mem_future (t : ℝ≥0) (f : brownianIntegralSpace B hBm P) :
    f - brownianTimeCutoff B hBm P t f ∈ brownianIntegralFutureSpace B hBm P t := by
  let tail : brownianIntegralSpace B hBm P →L[ℝ] brownianIntegralSpace B hBm P :=
    ContinuousLinearMap.id ℝ _ - brownianTimeCutoff B hBm P t
  let S := (brownianIntegralFutureSpace B hBm P t).comap tail.toLinearMap
  have hS : IsClosed (S : Set (brownianIntegralSpace B hBm P)) :=
    (Submodule.isClosed_topologicalClosure _).preimage tail.continuous
  apply brownianIntegralSpace_mem_of_generators S hS _ f
  intro a
  change brownianIntegralGenerator a - brownianTimeCutoff B hBm P t (brownianIntegralGenerator a) ∈
    brownianIntegralFutureSpace B hBm P t
  by_cases hrt : a.right ≤ t
  · rw [brownianTimeCutoff_generator_full a hrt, sub_self]
    exact (brownianIntegralFutureSpace B hBm P t).zero_mem
  · have htr : t ≤ a.right := le_of_not_ge hrt
    by_cases hlt : a.left ≤ t
    · rw [brownianTimeCutoff_generator a hlt]
      have he := brownianIntegralGenerator_refinement a t hlt htr
      have hdiff : brownianIntegralGenerator a - brownianIntegralGenerator (a.refineLeft t hlt) =
          brownianIntegralGenerator (a.refineRight t hlt htr) := by
        rw [he, add_sub_cancel_left]
      simp only [min_eq_right htr]
      rw [hdiff]
      exact brownianIntegralGenerator_mem_future _ le_rfl
    · rw [brownianTimeCutoff_generator_zero a (le_of_not_ge hlt), sub_zero]
      exact brownianIntegralGenerator_mem_future a (le_of_not_ge hlt)

end TimeTraps.Probability
