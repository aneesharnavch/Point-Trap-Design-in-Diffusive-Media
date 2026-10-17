module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

@[expose] public section

/-! Measurability of genuine path-measure families follows from their
finite observation measures. A measurable path embedding then transports
this conclusion to the original path Borel space. -/

namespace TimeTraps.Probability

open Set MeasureTheory

variable {Z Ω ι α : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace α]

omit [MeasurableSpace Ω] in
theorem projectiveLimit_family_measurable (μ : Z → Measure (ι → α))
    [∀ z, IsProbabilityMeasure (μ z)] (P : Z → ∀ I : Finset ι, Measure (I → α))
    (hproj : ∀ z, IsProjectiveLimit (μ z) (P z))
    (hP : ∀ I, Measurable (fun z => P z I)) : Measurable μ := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (generateFrom_measurableCylinders (α := fun _ : ι => α)).symm isPiSystem_measurableCylinders
  intro S hS
  obtain ⟨I, A, hA, rfl⟩ := (mem_measurableCylinders _).mp hS
  have he : (fun z => μ z (cylinder I A)) = fun z => P z I A :=
    funext (fun z => (hproj z).measure_cylinder I hA)
  rw [he]
  exact (Measure.measurable_coe hA).comp (hP I)

omit [MeasurableSpace α] in
theorem measure_family_measurable_of_embedding {B : Type*} [MeasurableSpace B]
    (μ : Z → Measure Ω) (Y : Ω → B) (hY : MeasurableEmbedding Y)
    (hmap : Measurable (fun z => (μ z).map Y)) : Measurable μ := by
  apply Measure.measurable_measure.mpr
  intro S hS
  have him : MeasurableSet (Y '' S) := hY.measurableSet_image' hS
  have he (z : Z) : (μ z).map Y (Y '' S) = μ z S := by
    rw [Measure.map_apply hY.measurable him, hY.injective.preimage_image]
  have hf : (fun z => μ z S) = fun z => (μ z).map Y (Y '' S) := funext (fun z => (he z).symm)
  rw [hf]
  exact (Measure.measurable_coe him).comp hmap

end TimeTraps.Probability
