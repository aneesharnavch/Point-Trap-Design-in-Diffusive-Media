module

public import TimeTraps.Probability.MarkovObservationAppendIndex
public import TimeTraps.Probability.MarkovFiniteKernelAppendData

@[expose] public section

/-! A chronological tuple extended by one state has exactly the original
finite observations and the newly appended final observation. -/

namespace TimeTraps.Probability

open MeasureTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def observationTupleSnoc (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t)
    (q : Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α) (y : α) :
    Fin (observationDurations 0 ((insert t I).sort (· ≤ ·))).length → α :=
  fun j => (Fin.snoc q y : Fin ((observationDurations 0 (I.sort (· ≤ ·))).length + 1) → α)
    ((observationAppendIndex I t ht).symm j)

theorem observationTupleSnoc_measurable (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t) :
    Measurable (fun p : (Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α) × α =>
      observationTupleSnoc I t ht p.1 p.2) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply ((observationAppendIndex I t ht).symm j)).comp
    (finiteStateSnoc_measurable _)

omit [MeasurableSpace α] in
theorem observationTupleSnoc_old (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t)
    (q : Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α) (y : α) (r : I) :
    observationState (insert t I) (observationTupleSnoc I t ht q y)
      ⟨r.val, Finset.mem_insert_of_mem r.property⟩ = observationState I q r := by
  let i := (observationTimeIndex I).symm r
  have he : observationTimeIndex (insert t I) (observationAppendIndex I t ht i.castSucc) =
      ⟨r.val, Finset.mem_insert_of_mem r.property⟩ := by
    apply Subtype.ext
    exact (observationAppendIndex_old_time I t ht i).trans
      (congrArg Subtype.val ((observationTimeIndex I).apply_symm_apply r))
  change (Fin.snoc q y : Fin ((observationDurations 0 (I.sort (· ≤ ·))).length + 1) → α)
    ((observationAppendIndex I t ht).symm
      ((observationTimeIndex (insert t I)).symm ⟨r.val, _⟩)) = q i
  rw [← he, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Fin.snoc_castSucc]

omit [MeasurableSpace α] in
theorem observationTupleSnoc_new (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t)
    (q : Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α) (y : α) :
    observationState (insert t I) (observationTupleSnoc I t ht q y)
      ⟨t, Finset.mem_insert_self t I⟩ = y := by
  have he : observationTimeIndex (insert t I) (observationAppendIndex I t ht
      (Fin.last (observationDurations 0 (I.sort (· ≤ ·))).length)) =
      ⟨t, Finset.mem_insert_self t I⟩ :=
    Subtype.ext (observationAppendIndex_new_time I t ht)
  change (Fin.snoc q y : Fin ((observationDurations 0 (I.sort (· ≤ ·))).length + 1) → α)
    ((observationAppendIndex I t ht).symm
      ((observationTimeIndex (insert t I)).symm ⟨t, _⟩)) = y
  rw [← he, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Fin.snoc_last]

end TimeTraps.Probability
