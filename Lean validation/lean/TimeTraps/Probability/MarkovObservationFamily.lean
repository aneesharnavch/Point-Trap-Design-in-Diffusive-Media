module

public import TimeTraps.Probability.MarkovObservationState
public import Mathlib.MeasureTheory.Constructions.Projective

@[expose] public section

/-! The genuine finite-set observation laws of a Markov semigroup.
Projectivity is derived from sorted elapsed-time pruning and exact
coordinate restriction, with no projectivity hypothesis on the laws. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def markovObservationKernel (K : ℝ≥0 → Kernel α α) (I : Finset ℝ≥0) :
    Kernel α (I → α) :=
  (finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·)))).map (observationState I)

noncomputable def markovObservationFamily (K : ℝ≥0 → Kernel α α) (x : α)
    (I : Finset ℝ≥0) : Measure (I → α) := markovObservationKernel K I x

theorem markovObservationKernel_probability (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (I : Finset ℝ≥0) :
    IsMarkovKernel (markovObservationKernel K I) := by
  unfold markovObservationKernel
  exact Kernel.IsMarkovKernel.map _ (observationState_measurable I)

theorem markovObservationFamily_probability (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (I : Finset ℝ≥0) :
    IsProbabilityMeasure (markovObservationFamily K x I) := by
  let := markovObservationKernel_probability K I
  unfold markovObservationFamily
  infer_instance

theorem markovObservationKernel_restrict (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)]
    (hadd : ∀ s t, K (s + t) = K t ∘ₖ K s)
    {I J : Finset ℝ≥0} (h : J ⊆ I) :
    (markovObservationKernel K I).map (Finset.restrict₂ (π := fun _ => α) h) = markovObservationKernel K J := by
  obtain ⟨p⟩ := observationTimeIndex_pruning h
  have hm : Measurable (Finset.restrict₂ (π := fun _ => α) h : (I → α) → (J → α)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  unfold markovObservationKernel
  rw [← Kernel.map_comp_right _ (observationState_measurable I) hm,
    ← observationState_pruning h p,
    Kernel.map_comp_right _ p.stateMap_measurable (observationState_measurable J),
    p.kernel_consistency K hadd]

theorem markovObservationFamily_projective (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)]
    (hadd : ∀ s t, K (s + t) = K t ∘ₖ K s) (x : α) :
    IsProjectiveMeasureFamily (α := fun _ => α) (markovObservationFamily K x) := by
  intro I J h
  have hm : Measurable (Finset.restrict₂ (π := fun _ => α) h : (I → α) → (J → α)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  exact (congrArg (fun k => k x) (markovObservationKernel_restrict K hadd h)).symm.trans
    (Kernel.map_apply _ hm x)

end TimeTraps.Probability
