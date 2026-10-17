module

public import TimeTraps.Probability.FiniteObservationSampling

@[expose] public section

/-! Recovering the original finite observation law from any countable
projective extension that contains those observation times. -/

namespace TimeTraps.Probability

open MeasureTheory

variable {β α : Type*} [DecidableEq β] [MeasurableSpace α]

theorem observationFamilyPullback_map_reverse (τ : ℕ → β)
    (P : ∀ I : Finset β, Measure (I → α)) (I : Finset β) (J : Finset ℕ)
    (himage : J.image τ = I) (r : I → J) (hr : ∀ i, τ (r i).val = i.val) :
    (observationFamilyPullback τ P J).map (fun q i => q (r i)) = P I := by
  subst I
  have hm : Measurable (fun q : J → α => fun i => q (r i)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  unfold observationFamilyPullback
  rw [Measure.map_map hm (observationPullbackState_measurable τ J)]
  have he : (fun q : J → α => fun i => q (r i)) ∘ observationPullbackState τ J = id := by
    funext q i
    change q ⟨τ (r i).val, _⟩ = q i
    exact congrArg q (Subtype.ext (hr i))
  rw [he, Measure.map_id]

theorem projectiveObservation_finite_recovery (b₀ : β)
    {P : ∀ I : Finset β, Measure (I → α)} (I : Finset β) {μ : Measure (ℕ → α)}
    (hμ : IsProjectiveLimit μ (observationFamilyPullback (finiteObservationSampling b₀ I) P)) :
    μ.map (fun q i => q (finiteObservationSamplingIndex I i).val) = P I := by
  let J := Finset.range I.card
  have hm : Measurable (fun q : J → α => fun i => q (finiteObservationSamplingIndex I i)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have he := observationFamilyPullback_map_reverse (finiteObservationSampling b₀ I) P I J
    (finiteObservationSampling_range b₀ I) (finiteObservationSamplingIndex I)
    (finiteObservationSampling_index b₀ I)
  rw [← hμ J, Measure.map_map hm (measurable_pi_lambda _ (fun _ => measurable_pi_apply _))] at he
  exact he

end TimeTraps.Probability
