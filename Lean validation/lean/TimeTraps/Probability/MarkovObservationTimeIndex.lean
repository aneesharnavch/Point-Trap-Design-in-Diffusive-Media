module

public import TimeTraps.Probability.MarkovObservationTimeRecovery
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! A finite set of observation times has a canonical coordinate system:
its sorted elapsed intervals, tagged by their actual cumulative times.
Subset restriction is realized by the already proved elapsed pruning. -/

namespace TimeTraps.Probability

open scoped NNReal

noncomputable def observationTimeIndex (I : Finset ℝ≥0) :
    Fin (observationDurations 0 (I.sort (· ≤ ·))).length ≃ I :=
  (observationDurationIndex 0 (I.sort (· ≤ ·))).trans
    (((I.sort_nodup (· ≤ ·)).getEquiv (I.sort (· ≤ ·))).trans
      (Equiv.subtypeEquivRight fun _ => Finset.mem_sort (· ≤ ·)))

theorem observationTimeIndex_time (I : Finset ℝ≥0)
    (i : Fin (observationDurations 0 (I.sort (· ≤ ·))).length) :
    (observationTimeIndex I i).val =
      elapsedObservationTime 0 (observationDurations 0 (I.sort (· ≤ ·))) i := by
  exact (elapsedObservationTime_recovery 0 _ (fun _ _ => zero_le)
    (I.pairwise_sort (· ≤ ·)) i).symm

theorem observationTimeIndex_sublist {I J : Finset ℝ≥0} (h : J ⊆ I) :
    List.Sublist (J.sort (· ≤ ·)) (I.sort (· ≤ ·)) := by
  apply List.sublist_of_subperm_of_sortedLE
  · apply List.subperm_of_subset (J.sort_nodup (· ≤ ·))
    intro t ht
    exact (Finset.mem_sort (· ≤ ·)).mpr (h ((Finset.mem_sort (· ≤ ·)).mp ht))
  · exact (J.pairwise_sort (· ≤ ·)).sortedLE
  · exact (I.pairwise_sort (· ≤ ·)).sortedLE

theorem observationTimeIndex_pruning {I J : Finset ℝ≥0} (h : J ⊆ I) :
    Nonempty (ElapsedObservationPruning
      (observationDurations 0 (I.sort (· ≤ ·)))
      (observationDurations 0 (J.sort (· ≤ ·)))) :=
  elapsedObservationPruning_of_sublist (observationTimeIndex_sublist h) 0
    (fun _ _ => zero_le) (I.pairwise_sort (· ≤ ·))

theorem observationTimeIndex_pruning_index {I J : Finset ℝ≥0} (h : J ⊆ I)
    (p : ElapsedObservationPruning
      (observationDurations 0 (I.sort (· ≤ ·)))
      (observationDurations 0 (J.sort (· ≤ ·)))) (j : J) :
    observationTimeIndex I (p.index ((observationTimeIndex J).symm j)) =
      ⟨j.val, h j.property⟩ := by
  apply Subtype.ext
  rw [observationTimeIndex_time]
  rw [← p.stateMap_apply (elapsedObservationTime 0
    (observationDurations 0 (I.sort (· ≤ ·)))) ((observationTimeIndex J).symm j),
    p.time_coordinates]
  rw [← observationTimeIndex_time]
  exact congrArg Subtype.val ((observationTimeIndex J).apply_symm_apply j)

end TimeTraps.Probability
