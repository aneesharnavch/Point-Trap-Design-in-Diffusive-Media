module

public import TimeTraps.Probability.ProjectiveObservationReindex
public import TimeTraps.Probability.MarkovSampledPathLaw

@[expose] public section

/-! The constructed Markov sampled path law commutes with every countable
reindexing, by its actual finite marginals and projective uniqueness. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

theorem markovSampledPathLaw_reindex (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)]
    (hadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    (τ : ℕ → ℝ≥0) (r : ℕ → ℕ) (x : α) :
    (markovSampledPathLaw K τ x).map (fun q => q ∘ r) =
      markovSampledPathLaw K (τ ∘ r) x := by
  let inst : ∀ I, IsProbabilityMeasure
      (observationFamilyPullback (τ ∘ r) (markovObservationFamily K x) I) :=
    markovSampledFamily_probability K (τ ∘ r) x
  have hm := projectiveObservation_reindex τ r
    (markovSampledPathLaw_isProjectiveLimit K hadd τ x)
  exact hm.unique (markovSampledPathLaw_isProjectiveLimit K hadd (τ ∘ r) x)

end TimeTraps.Probability
