module

public import TimeTraps.Probability.ProjectiveObservationPullback

@[expose] public section

/-! Reindexing a countably sampled projective law, including maps that
repeat or omit coordinates. No injectivity of the reindexing is required. -/

namespace TimeTraps.Probability

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [DecidableEq β]

theorem observationFamilyPullback_comp (τ : ℕ → β) (r : ℕ → ℕ)
    (P : ∀ I : Finset β, Measure (I → α)) (I : Finset ℕ) :
    observationFamilyPullback r (observationFamilyPullback τ P) I =
      observationFamilyPullback (τ ∘ r) P I := by
  unfold observationFamilyPullback
  rw [Measure.map_map (observationPullbackState_measurable r I)
    (observationPullbackState_measurable τ (I.image r))]
  dsimp only [Function.comp_def, observationPullbackState]
  have htransport (J : Finset β) (hJ : J = I.image (τ ∘ r))
      (hm : ∀ i : I, τ (r i.val) ∈ J) :
      (P J).map (fun q i => q ⟨τ (r i.val), hm i⟩) =
        (P (I.image (τ ∘ r))).map
          (fun q i => q ⟨τ (r i.val), hJ ▸ hm i⟩) := by
    subst J
    rfl
  exact htransport _ (by rw [Finset.image_image]) _

theorem projectiveObservation_reindex (τ : ℕ → β) (r : ℕ → ℕ)
    {P : ∀ I : Finset β, Measure (I → α)} {μ : Measure (ℕ → α)}
    (hμ : IsProjectiveLimit μ (observationFamilyPullback τ P)) :
    IsProjectiveLimit (μ.map (fun q => q ∘ r)) (observationFamilyPullback (τ ∘ r) P) := by
  intro I
  have hR : Measurable (fun q : ℕ → α => q ∘ r) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hI : Measurable (I.restrict : (ℕ → α) → (I → α)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hJ : Measurable ((I.image r).restrict : (ℕ → α) → ((I.image r) → α)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  calc
    _ = μ.map (I.restrict ∘ (fun q => q ∘ r)) := Measure.map_map hI hR
    _ = (μ.map (I.image r).restrict).map (observationPullbackState r I) :=
      (Measure.map_map (observationPullbackState_measurable r I) hJ).symm
    _ = (observationFamilyPullback τ P (I.image r)).map (observationPullbackState r I) :=
      congrArg (fun ν => ν.map (observationPullbackState r I)) (hμ (I.image r))
    _ = _ := observationFamilyPullback_comp τ r P I

end TimeTraps.Probability
