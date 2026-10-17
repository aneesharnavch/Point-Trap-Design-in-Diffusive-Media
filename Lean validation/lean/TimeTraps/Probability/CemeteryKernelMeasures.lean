module

public import TimeTraps.Probability.CemeteryKernelData

@[expose] public section

/-! Live-state restrictions and uniqueness of the one-point probability
completion. The cemetery atom is fixed by total mass and the live measure. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem cemeteryMeasure_live_set (μ : Measure α) {A : Set α} (hA : MeasurableSet A) :
    cemeteryMeasure μ (Sum.inl '' A) = μ A := by
  rw [cemeteryMeasure_apply μ hA.inl_image]
  simp only [Sum.inl_injective.preimage_image, mem_image, Sum.inl_ne_inr, and_false,
    exists_false, not_false_eq_true, indicator_of_notMem, mul_zero, add_zero]

theorem cemeteryKernel_live_set (κ : Kernel α α) (x : α) {A : Set α} (hA : MeasurableSet A) :
    cemeteryKernel κ (Sum.inl x) (Sum.inl '' A) = κ x A :=
  cemeteryMeasure_live_set (κ x) hA

theorem cemeteryKernel_dead_live_set (κ : Kernel α α) {A : Set α} (hA : MeasurableSet A) :
    cemeteryKernel κ (Sum.inr ()) (Sum.inl '' A) = 0 := by
  rw [cemeteryKernel_dead, Measure.dirac_apply' _ hA.inl_image]
  simp only [mem_image, Sum.inl_ne_inr, and_false, exists_false, not_false_eq_true,
    indicator_of_notMem]

omit [MeasurableSpace α] in
theorem cemetery_dead_complement : ({Sum.inr ()} : Set (α ⊕ Unit)) = (range Sum.inl)ᶜ := by
  ext z
  cases z with
  | inl a => simp
  | inr u => cases u; simp

theorem cemeteryProbability_dead_mass (μ : Measure (α ⊕ Unit)) [IsProbabilityMeasure μ] :
    μ {Sum.inr ()} = 1 - μ (range Sum.inl) := by
  rw [cemetery_dead_complement,
    measure_compl measurableSet_range_inl (measure_ne_top μ _), measure_univ]

theorem cemeteryProbability_ext {μ ν : Measure (α ⊕ Unit)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (he : ∀ A : Set α, MeasurableSet A → μ (Sum.inl '' A) = ν (Sum.inl '' A)) : μ = ν := by
  have hl : μ (range Sum.inl) = ν (range Sum.inl) := by
    simpa only [image_univ] using he univ MeasurableSet.univ
  have hd : μ {Sum.inr ()} = ν {Sum.inr ()} := by
    rw [cemeteryProbability_dead_mass, cemeteryProbability_dead_mass, hl]
  have hdm : MeasurableSet ({Sum.inr ()} : Set (α ⊕ Unit)) := by
    rw [cemetery_dead_complement]
    exact measurableSet_range_inl.compl
  apply Measure.ext
  intro A hA
  have hpre : MeasurableSet (Sum.inl ⁻¹' A) := measurable_inl hA
  by_cases hdead : Sum.inr () ∈ A
  · have heq : A = Sum.inl '' (Sum.inl ⁻¹' A) ∪ {Sum.inr ()} := by
      ext z
      cases z with
      | inl a => simp
      | inr u => cases u; simp [hdead]
    have hdis : Disjoint (Sum.inl '' (Sum.inl ⁻¹' A)) ({Sum.inr ()} : Set (α ⊕ Unit)) := by
      apply disjoint_left.mpr
      rintro z ⟨a, _, rfl⟩ hz
      simp only [mem_singleton_iff, Sum.inl_ne_inr] at hz
    rw [heq, measure_union hdis hdm, measure_union hdis hdm, he _ hpre, hd]
  · have heq : A = Sum.inl '' (Sum.inl ⁻¹' A) := by
      ext z
      cases z with
      | inl a => simp
      | inr u => cases u; simp [hdead]
    rw [heq]
    exact he _ hpre

end TimeTraps.Probability
