module

public import TimeTraps.Probability.MarkovObservationFamily
public import TimeTraps.Probability.ProjectiveObservationPullback
public import TimeTraps.Probability.CountableProjectiveExtension

@[expose] public section

/-! A genuine countably sampled path law constructed from the original
Markov transition kernels. All finite marginals come from the actual
chronological transitions; projectivity is proved, rather than assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def markovSampledFamily (K : ℝ≥0 → Kernel α α) (τ : ℕ → ℝ≥0)
    (x : α) (I : Finset ℕ) : Measure (I → α) :=
  observationFamilyPullback τ (markovObservationFamily K x) I

theorem markovSampledFamily_probability (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (τ : ℕ → ℝ≥0) (x : α) (I : Finset ℕ) :
    IsProbabilityMeasure (markovSampledFamily K τ x I) := by
  let inst : ∀ J, IsProbabilityMeasure (markovObservationFamily K x J) :=
    markovObservationFamily_probability K x
  exact observationFamilyPullback_probability τ _ I

theorem markovSampledFamily_projective (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)]
    (hadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (τ : ℕ → ℝ≥0) (x : α) :
    IsProjectiveMeasureFamily (α := fun _ => α) (markovSampledFamily K τ x) :=
  observationFamilyPullback_projective τ (markovObservationFamily_projective K hadd x)

variable [StandardBorelSpace α] [Nonempty α]

noncomputable def markovSampledPathLaw (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (τ : ℕ → ℝ≥0) (x : α) : Measure (ℕ → α) := by
  let inst : ∀ I, IsProbabilityMeasure (markovSampledFamily K τ x I) :=
    markovSampledFamily_probability K τ x
  exact borelCountableExtension α (markovSampledFamily K τ x)

theorem markovSampledPathLaw_probability (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (τ : ℕ → ℝ≥0) (x : α) :
    IsProbabilityMeasure (markovSampledPathLaw K τ x) := by
  unfold markovSampledPathLaw
  infer_instance

theorem markovSampledPathLaw_isProjectiveLimit (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)]
    (hadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (τ : ℕ → ℝ≥0) (x : α) :
    IsProjectiveLimit (markovSampledPathLaw K τ x) (markovSampledFamily K τ x) := by
  let inst : ∀ I, IsProbabilityMeasure (markovSampledFamily K τ x I) :=
    markovSampledFamily_probability K τ x
  exact borelCountableExtension_isProjectiveLimit α _ (markovSampledFamily_projective K hadd τ x)

end TimeTraps.Probability
