module

public import TimeTraps.Probability.MarkovObservationFamily

@[expose] public section

/-! Appending the latest chronological observation retains the exact
old durations and adds the elapsed interval from its final old time. -/

namespace TimeTraps.Probability

open scoped NNReal

def observationLastTime : ℝ≥0 → List ℝ≥0 → ℝ≥0
  | s, [] => s
  | _, t :: d => observationLastTime t d

theorem observationDurations_append_singleton (s t : ℝ≥0) (d : List ℝ≥0) :
    observationDurations s (d ++ [t]) =
      observationDurations s d ++ [t - observationLastTime s d] := by
  induction d generalizing s with
  | nil => rfl
  | cons u d ih => simp only [List.cons_append, observationDurations, observationLastTime, ih]

theorem observationLastTime_le (s r : ℝ≥0) (d : List ℝ≥0)
    (hs : s ≤ r) (hd : ∀ u ∈ d, u ≤ r) : observationLastTime s d ≤ r := by
  induction d generalizing s with
  | nil => exact hs
  | cons u d ih =>
      exact ih u (hd u List.mem_cons_self)
        (fun v hv => hd v (List.mem_cons_of_mem u hv))

theorem le_observationLastTime (s : ℝ≥0) (d : List ℝ≥0)
    (hs : ∀ u ∈ d, s ≤ u) (hd : d.Pairwise (· ≤ ·)) : s ≤ observationLastTime s d := by
  induction d generalizing s with
  | nil => exact le_rfl
  | cons u d ih =>
      obtain ⟨hu, hp⟩ := List.pairwise_cons.mp hd
      exact (hs u List.mem_cons_self).trans (ih u hu hp)

theorem member_le_observationLastTime (s : ℝ≥0) (d : List ℝ≥0)
    (hd : d.Pairwise (· ≤ ·)) {u : ℝ≥0} (hu : u ∈ d) : u ≤ observationLastTime s d := by
  induction d generalizing s with
  | nil => exact (List.not_mem_nil hu).elim
  | cons v d ih =>
      obtain ⟨hv, hp⟩ := List.pairwise_cons.mp hd
      rcases List.mem_cons.mp hu with he | hu
      · subst u
        exact le_observationLastTime v d hv hp
      · exact ih v hp hu

theorem observationLastTime_sorted_max (I : Finset ℝ≥0) {s : ℝ≥0}
    (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s) :
    observationLastTime 0 (I.sort (· ≤ ·)) = s := by
  apply le_antisymm
  · exact observationLastTime_le 0 s _ zero_le
      (fun u hu => hmax u ((Finset.mem_sort (· ≤ ·)).mp hu))
  · exact member_le_observationLastTime 0 _ (I.pairwise_sort (· ≤ ·))
      ((Finset.mem_sort (· ≤ ·)).mpr hs)

theorem observation_sort_insert_last (I : Finset ℝ≥0) {t : ℝ≥0}
    (ht : ∀ u ∈ I, u < t) :
    (insert t I).sort (· ≤ ·) = I.sort (· ≤ ·) ++ [t] := by
  classical
  have hn : t ∉ I := fun hm => (lt_irrefl t) (ht t hm)
  have hd : (I.sort (· ≤ ·) ++ [t]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨I.sort_nodup (· ≤ ·), by simp, ?_⟩
    intro u hu v hv he
    have hv' : v = t := List.mem_singleton.mp hv
    exact hn ((he.trans hv') ▸ (Finset.mem_sort (· ≤ ·)).mp hu)
  have hp : (I.sort (· ≤ ·) ++ [t]).Pairwise (· ≤ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨I.pairwise_sort (· ≤ ·), by simp, ?_⟩
    intro u hu v hv
    have he : v = t := List.mem_singleton.mp hv
    subst v
    exact (ht u ((Finset.mem_sort (· ≤ ·)).mp hu)).le
  have he : (I.sort (· ≤ ·) ++ [t]).toFinset = insert t I := by simp
  rw [← he]
  exact (List.toFinset_sort (· ≤ ·) hd).mpr hp

end TimeTraps.Probability
