module

public import TimeTraps.Probability.BrownianDenseContinuityRecovery

@[expose] public section

/-! Reindexing and exact finite marginals of the constructed sequence laws.
Repeated indices and repeated times are allowed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable def brownianIndexProjection (f : ℕ → ℕ) (I : Finset ℕ) :
    (I.image f → ℝ) → (I → ℝ) :=
  fun x i => x ⟨f i, Finset.mem_image.mpr ⟨i, i.prop, rfl⟩⟩

theorem brownianIndexProjection_measurable (f : ℕ → ℕ) (I : Finset ℕ) :
    Measurable (brownianIndexProjection f I) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

theorem brownianProjectiveFamily_map_eval_congr {ι : Type*} {I J : Finset ℝ≥0}
    (h : I = J) (t : ι → ℝ≥0) (hI : ∀ i, t i ∈ I) (hJ : ∀ i, t i ∈ J) :
    (BrownianReal.projectiveFamily I).map (fun x : I → ℝ => fun i => x ⟨t i, hI i⟩) =
      (BrownianReal.projectiveFamily J).map (fun x : J → ℝ => fun i => x ⟨t i, hJ i⟩) := by
  subst J
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem brownianSequenceFamily_reindex (τ : ℕ → ℝ≥0) (f : ℕ → ℕ) (I : Finset ℕ) :
    (brownianSequenceFamily τ (I.image f)).map (brownianIndexProjection f I) =
      brownianSequenceFamily (τ ∘ f) I := by
  rw [brownianSequenceFamily, Measure.map_map (brownianIndexProjection_measurable f I)
    (brownianTimeProjection_measurable τ (I.image f)), brownianSequenceFamily]
  unfold brownianIndexProjection brownianTimeProjection
  exact brownianProjectiveFamily_map_eval_congr Finset.image_image
    (fun i : I => τ (f i)) _ _

theorem brownianSequence_reindex_hasLaw (τ : ℕ → ℝ≥0) (f : ℕ → ℕ) :
    HasLaw (fun ω : ℕ → ℝ => fun n => ω (f n))
      (brownianSequenceMeasure (τ ∘ f)) (brownianSequenceMeasure τ) := by
  have hm : Measurable (fun ω : ℕ → ℝ => fun n => ω (f n)) := by fun_prop
  refine ⟨hm.aemeasurable, ?_⟩
  have hP : IsProjectiveLimit
      ((brownianSequenceMeasure τ).map (fun ω : ℕ → ℝ => fun n => ω (f n)))
      (brownianSequenceFamily (τ ∘ f)) := by
    intro I
    have h : HasLaw (brownianIndexProjection f I) (brownianSequenceFamily (τ ∘ f) I)
        (brownianSequenceFamily τ (I.image f)) :=
      ⟨(brownianIndexProjection_measurable f I).aemeasurable,
        brownianSequenceFamily_reindex τ f I⟩
    have he := (h.comp (brownianSequence_hasLaw τ (I.image f))).map_eq
    rw [Measure.map_map (by fun_prop) hm]
    exact he
  exact hP.unique (gaussianCountableExtension_isProjectiveLimit
    (brownianSequenceFamily (τ ∘ f)) (brownianSequenceFamily_projective (τ ∘ f)))

end TimeTraps.Probability
