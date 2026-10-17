module

public import TimeTraps.Probability.ProjectiveObservationFiniteRecovery

@[expose] public section

/-! A process whose every countable sampling has the stated projective
laws has those exact laws on every finite set of original times. -/

namespace TimeTraps.Probability

open MeasureTheory

variable {Ω β α : Type*} [MeasurableSpace Ω] [DecidableEq β] [MeasurableSpace α]

theorem finite_laws_of_countable_projective_observations (b₀ : β)
    (μ : Measure Ω) (X : β → Ω → α) (P : ∀ I : Finset β, Measure (I → α))
    (hX : ∀ t, Measurable (X t))
    (hμ : ∀ τ : ℕ → β, IsProjectiveLimit (μ.map (fun ω i => X (τ i) ω))
      (observationFamilyPullback τ P)) (I : Finset β) :
    μ.map (fun ω (i : I) => X i ω) = P I := by
  let τ := finiteObservationSampling b₀ I
  have h := projectiveObservation_finite_recovery b₀ I (hμ τ)
  have hm : Measurable (fun q : ℕ → α => fun i => q (finiteObservationSamplingIndex I i).val) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [Measure.map_map hm (measurable_pi_lambda _ (fun i => hX (τ i)))] at h
  simpa only [Function.comp_def, τ, finiteObservationSampling_index] using h

end TimeTraps.Probability
