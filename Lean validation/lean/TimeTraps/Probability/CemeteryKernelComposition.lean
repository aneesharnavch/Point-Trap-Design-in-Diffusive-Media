module

public import TimeTraps.Probability.CemeteryKernelMeasures

@[expose] public section

/-! One-point probability completion respects composition and identity.
The dead state is absorbing and the original live transitions are exact. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem subprobabilityKernel_comp_bound (κ η : Kernel α α)
    (hκ : ∀ x, κ x univ ≤ 1) (hη : ∀ x, η x univ ≤ 1) (x : α) :
    (η ∘ₖ κ) x univ ≤ 1 := by
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  calc
    _ ≤ ∫⁻ _, 1 ∂κ x := lintegral_mono hη
    _ = κ x univ := by simp only [lintegral_const, one_mul]
    _ ≤ 1 := hκ x

theorem cemeteryKernel_comp (κ η : Kernel α α)
    (hκ : ∀ x, κ x univ ≤ 1) (hη : ∀ x, η x univ ≤ 1) :
    cemeteryKernel η ∘ₖ cemeteryKernel κ = cemeteryKernel (η ∘ₖ κ) := by
  let : IsMarkovKernel (cemeteryKernel κ) := cemeteryKernel_isMarkov κ hκ
  let : IsMarkovKernel (cemeteryKernel η) := cemeteryKernel_isMarkov η hη
  let : IsMarkovKernel (cemeteryKernel (η ∘ₖ κ)) :=
    cemeteryKernel_isMarkov _ (subprobabilityKernel_comp_bound κ η hκ hη)
  apply Kernel.ext
  intro z
  cases z with
  | inl x =>
    apply cemeteryProbability_ext
    intro A hA
    rw [Kernel.comp_apply' _ _ _ hA.inl_image, cemeteryKernel_live,
      cemeteryMeasure_lintegral _ ((cemeteryKernel η).measurable_coe hA.inl_image),
      cemeteryKernel_dead_live_set η hA, mul_zero, add_zero,
      cemeteryKernel_live_set _ x hA, Kernel.comp_apply' _ _ _ hA]
    apply lintegral_congr
    intro y
    exact cemeteryKernel_live_set η y hA
  | inr u =>
    cases u
    apply Measure.ext
    intro A hA
    rw [Kernel.comp_apply' _ _ _ hA, cemeteryKernel_dead κ,
      lintegral_dirac' _ ((cemeteryKernel η).measurable_coe hA),
      cemeteryKernel_dead η, cemeteryKernel_dead (η ∘ₖ κ)]

theorem cemeteryMeasure_dirac (x : α) :
    cemeteryMeasure (Measure.dirac x) = Measure.dirac (Sum.inl x : α ⊕ Unit) := by
  rw [cemeteryMeasure, Measure.map_dirac' measurable_inl x,
    Measure.dirac_apply_of_mem (mem_univ x), tsub_self, zero_smul, add_zero]

theorem cemeteryKernel_id : cemeteryKernel (Kernel.id : Kernel α α) = Kernel.id := by
  apply Kernel.ext
  intro z
  cases z with
  | inl x => rw [cemeteryKernel_live, Kernel.id_apply, cemeteryMeasure_dirac, Kernel.id_apply]
  | inr u => cases u; rw [cemeteryKernel_dead, Kernel.id_apply]

end TimeTraps.Probability
