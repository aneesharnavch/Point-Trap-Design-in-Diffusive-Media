module

public import TimeTraps.Probability.MarkovObservationAppendTime
public import TimeTraps.Probability.MarkovObservationInverse

@[expose] public section

/-! Exact time labels of the old and newly appended canonical tuple
coordinates. These identities connect the chronological append law to
finite past events without changing the observation convention. -/

namespace TimeTraps.Probability

open scoped NNReal

theorem observationTimeIndex_getElem (I : Finset ℝ≥0)
    (i : Fin (observationDurations 0 (I.sort (· ≤ ·))).length) :
    (observationTimeIndex I i).val = (I.sort (· ≤ ·))[i.val]'(by
      simpa only [observationDurations_length] using i.isLt) := rfl

theorem observationTimeIndex_getElemBang (I : Finset ℝ≥0)
    (i : Fin (observationDurations 0 (I.sort (· ≤ ·))).length) :
    (observationTimeIndex I i).val = (I.sort (· ≤ ·))[i.val]! := by
  have hi : i.val < (I.sort (· ≤ ·)).length := by
    simpa only [observationDurations_length] using i.isLt
  rw [getElem!_pos (I.sort (· ≤ ·)) i.val hi]
  exact observationTimeIndex_getElem I i

noncomputable def observationAppendIndex (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t) :
    Fin ((observationDurations 0 (I.sort (· ≤ ·))).length + 1) ≃
      Fin (observationDurations 0 ((insert t I).sort (· ≤ ·))).length :=
  finCongr (by simp only [observationDurations_length, observation_sort_insert_last I ht,
    List.length_append, List.length_singleton])

theorem observationAppendIndex_val (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t)
    (i : Fin ((observationDurations 0 (I.sort (· ≤ ·))).length + 1)) :
    (observationAppendIndex I t ht i).val = i.val := rfl

theorem observationAppendIndex_old_time (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t)
    (i : Fin (observationDurations 0 (I.sort (· ≤ ·))).length) :
    (observationTimeIndex (insert t I) (observationAppendIndex I t ht i.castSucc)).val =
      (observationTimeIndex I i).val := by
  rw [observationTimeIndex_getElemBang, observationTimeIndex_getElemBang]
  simp only [observationAppendIndex_val, Fin.val_castSucc]
  rw [observation_sort_insert_last I ht]
  have hi : i.val < (I.sort (· ≤ ·)).length := by
    simpa only [observationDurations_length] using i.isLt
  have hj : i.val < (I.sort (· ≤ ·) ++ [t]).length := by
    simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt hi
  rw [getElem!_pos (I.sort (· ≤ ·) ++ [t]) i.val hj, getElem!_pos (I.sort (· ≤ ·)) i.val hi, List.getElem_append_left hi]

theorem observationAppendIndex_new_time (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t) :
    (observationTimeIndex (insert t I) (observationAppendIndex I t ht
      (Fin.last (observationDurations 0 (I.sort (· ≤ ·))).length))).val = t := by
  rw [observationTimeIndex_getElemBang]
  simp only [observationAppendIndex_val, Fin.val_last, observationDurations_length]
  rw [observation_sort_insert_last I ht]
  rw [getElem!_pos (I.sort (· ≤ ·) ++ [t]) (I.sort (· ≤ ·)).length (by simp : (I.sort (· ≤ ·)).length < (I.sort (· ≤ ·) ++ [t]).length),
    List.getElem_append_right le_rfl]
  simp

end TimeTraps.Probability
