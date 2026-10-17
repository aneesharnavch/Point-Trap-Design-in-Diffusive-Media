module

public import TimeTraps.Probability.MarkovObservationAppendIndex
public import TimeTraps.Probability.MarkovFiniteKernelAppendData

@[expose] public section

/-! When a finite history includes its maximum time, the last state in
its chronological tuple is exactly the canonical observation there. -/

namespace TimeTraps.Probability

open scoped NNReal

variable {α : Type*}

theorem finiteStateLast_eq_final (x : α) {n : ℕ} (hn : 0 < n) (q : Fin n → α) :
    finiteStateLast x q = q ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ := by
  cases n with
  | zero => exact (lt_irrefl 0 hn).elim
  | succ n => rfl

theorem observationTimeIndex_final_time (I : Finset ℝ≥0) {s : ℝ≥0}
    (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s) :
    (observationTimeIndex I ⟨(observationDurations 0 (I.sort (· ≤ ·))).length - 1,
      by simp only [observationDurations_length, Finset.length_sort];
         exact Nat.sub_lt (Finset.card_pos.mpr ⟨s, hs⟩) Nat.zero_lt_one⟩).val = s := by
  rw [observationTimeIndex_getElem]
  simp only [observationDurations_length]
  rw [Finset.sorted_last_eq_max'_aux I _ ⟨s, hs⟩]
  apply le_antisymm
  · exact hmax _ (I.max'_mem ⟨s, hs⟩)
  · exact I.le_max' s hs

theorem finiteStateLast_observationState (x : α) (I : Finset ℝ≥0) {s : ℝ≥0}
    (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s)
    (q : Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α) :
    finiteStateLast x q = observationState I q ⟨s, hs⟩ := by
  have hn : 0 < (observationDurations 0 (I.sort (· ≤ ·))).length := by
    simpa only [observationDurations_length, Finset.length_sort] using Finset.card_pos.mpr ⟨s, hs⟩
  rw [finiteStateLast_eq_final x hn]
  have he : observationTimeIndex I ⟨(observationDurations 0 (I.sort (· ≤ ·))).length - 1,
      Nat.sub_lt hn Nat.zero_lt_one⟩ = ⟨s, hs⟩ :=
    Subtype.ext (observationTimeIndex_final_time I hs hmax)
  change q _ = q ((observationTimeIndex I).symm ⟨s, hs⟩)
  rw [← he, Equiv.symm_apply_apply]

end TimeTraps.Probability
