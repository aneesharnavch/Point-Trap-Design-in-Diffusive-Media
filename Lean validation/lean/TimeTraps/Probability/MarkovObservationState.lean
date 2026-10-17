module

public import TimeTraps.Probability.MarkovObservationTimeIndex

@[expose] public section

/-! Reindexing a sorted finite trajectory by the actual finite time set
is measurable, and elapsed pruning becomes literal coordinate restriction. -/

namespace TimeTraps.Probability

open MeasureTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def observationState (I : Finset ℝ≥0)
    (q : Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α) : I → α :=
  fun t => q ((observationTimeIndex I).symm t)

theorem observationState_measurable (I : Finset ℝ≥0) :
    Measurable (observationState (α := α) I) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

omit [MeasurableSpace α] in
theorem observationState_pruning {I J : Finset ℝ≥0} (h : J ⊆ I)
    (p : ElapsedObservationPruning
      (observationDurations 0 (I.sort (· ≤ ·)))
      (observationDurations 0 (J.sort (· ≤ ·)))) :
    observationState (α := α) J ∘ p.stateMap =
      (Finset.restrict₂ (π := fun _ => α) h : (I → α) → (J → α)) ∘ observationState I := by
  funext q j
  change p.stateMap q ((observationTimeIndex J).symm j) =
    q ((observationTimeIndex I).symm ⟨j.val, h j.property⟩)
  rw [p.stateMap_apply]
  congr 1
  exact (observationTimeIndex I).injective (by
    rw [(observationTimeIndex I).apply_symm_apply]
    exact observationTimeIndex_pruning_index h p j)

end TimeTraps.Probability
