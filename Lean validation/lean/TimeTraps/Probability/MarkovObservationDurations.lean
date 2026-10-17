module

public import TimeTraps.Probability.MarkovFiniteKernelPruning
public import Mathlib.Data.List.Sort

@[expose] public section

/-! Elapsed intervals for a sorted finite set of observation times.
Deleting a sorted sublist induces actual elapsed-time pruning, using
only the original order and addition/subtraction identities. -/

namespace TimeTraps.Probability

open scoped NNReal

noncomputable def ElapsedObservationPruning.refl :
    (d : List ℝ≥0) → ElapsedObservationPruning d d
  | [] => .empty []
  | t :: d => .keep t (ElapsedObservationPruning.refl d)

def observationDurations : ℝ≥0 → List ℝ≥0 → List ℝ≥0
  | _, [] => []
  | s, t :: d => (t - s) :: observationDurations t d

theorem observationDurations_length (s : ℝ≥0) (d : List ℝ≥0) :
    (observationDurations s d).length = d.length := by
  induction d generalizing s with
  | nil => rfl
  | cons t d ih => simp only [observationDurations, List.length_cons, ih]

theorem elapsedObservationPruning_start (s t : ℝ≥0) (hst : s ≤ t)
    (d : List ℝ≥0) (hd : ∀ u ∈ d, t ≤ u) :
    Nonempty (ElapsedObservationPruning ((t - s) :: observationDurations t d)
      (observationDurations s d)) := by
  cases d with
  | nil => exact ⟨.empty _⟩
  | cons u d =>
    have htu : t ≤ u := hd u (List.mem_cons_self)
    have he : (t - s) + (u - t) = u - s :=
      (add_comm _ _).trans (tsub_add_tsub_cancel htu hst)
    refine ⟨.merge (t - s) (u - t) (observationDurations u d)
      ((u - s) :: observationDurations u d) ?_⟩
    rw [he]
    exact ElapsedObservationPruning.refl _

theorem elapsedObservationPruning_of_sublist {d e : List ℝ≥0} (h : List.Sublist e d)
    (s : ℝ≥0) (hs : ∀ t ∈ d, s ≤ t) (hd : d.Pairwise (· ≤ ·)) :
    Nonempty (ElapsedObservationPruning (observationDurations s d) (observationDurations s e)) := by
  induction h generalizing s with
  | slnil => exact ⟨.empty []⟩
  | @cons e d t h ih =>
    obtain ⟨ht, hpair⟩ := List.pairwise_cons.mp hd
    obtain ⟨p⟩ := ih t ht hpair
    obtain ⟨q⟩ := elapsedObservationPruning_start s t (hs t List.mem_cons_self) e
      (fun u hu => ht u (h.subset hu))
    exact ⟨.trans (.keep (t - s) p) q⟩
  | @cons_cons e d t h ih =>
    obtain ⟨ht, hpair⟩ := List.pairwise_cons.mp hd
    obtain ⟨p⟩ := ih t ht hpair
    exact ⟨.keep (t - s) p⟩

end TimeTraps.Probability
