module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-! Pulling a projective family back along any observation-time map.
Repeated times are retained as equal coordinates through the finite image,
so no injectivity assumption is imposed on a sampling sequence. -/

namespace TimeTraps.Probability

open MeasureTheory

variable {ι β α : Type*} [DecidableEq β] [MeasurableSpace α]

noncomputable def observationPullbackState (τ : ι → β) (I : Finset ι)
    (q : (I.image τ) → α) : I → α :=
  fun i => q ⟨τ i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩

theorem observationPullbackState_measurable (τ : ι → β) (I : Finset ι) :
    Measurable (observationPullbackState (α := α) τ I) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

omit [MeasurableSpace α] in
theorem observationPullbackState_restrict (τ : ι → β) {I J : Finset ι} (h : J ⊆ I) :
    observationPullbackState (α := α) τ J ∘ Finset.restrict₂ (π := fun _ => α) (Finset.image_mono τ h) =
      Finset.restrict₂ (π := fun _ => α) h ∘ observationPullbackState τ I := rfl

noncomputable def observationFamilyPullback (τ : ι → β)
    (P : ∀ I : Finset β, Measure (I → α)) (I : Finset ι) : Measure (I → α) :=
  (P (I.image τ)).map (observationPullbackState τ I)

theorem observationFamilyPullback_probability (τ : ι → β)
    (P : ∀ I : Finset β, Measure (I → α)) [∀ I, IsProbabilityMeasure (P I)] (I : Finset ι) :
    IsProbabilityMeasure (observationFamilyPullback τ P I) := by
  unfold observationFamilyPullback
  exact Measure.isProbabilityMeasure_map (observationPullbackState_measurable τ I).aemeasurable

theorem observationFamilyPullback_projective (τ : ι → β)
    {P : ∀ I : Finset β, Measure (I → α)} (hP : IsProjectiveMeasureFamily (α := fun _ => α) P) :
    IsProjectiveMeasureFamily (α := fun _ => α) (observationFamilyPullback τ P) := by
  intro I J h
  have hm : Measurable (Finset.restrict₂ (π := fun _ => α) h : (I → α) → (J → α)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have him : Measurable (Finset.restrict₂ (π := fun _ => α) (Finset.image_mono τ h) :
      (I.image τ → α) → (J.image τ → α)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  unfold observationFamilyPullback
  rw [hP (I.image τ) (J.image τ) (Finset.image_mono τ h),
    Measure.map_map (observationPullbackState_measurable τ J) him,
    Measure.map_map hm (observationPullbackState_measurable τ I),
    observationPullbackState_restrict]

end TimeTraps.Probability
