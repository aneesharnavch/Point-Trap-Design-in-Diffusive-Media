module

public import TimeTraps.Probability.MarkovObservationTimeCoordinates

@[expose] public section

/-! For an ordered time list, cumulative sums of its elapsed intervals
recover the original observation times exactly, including an observation
at time zero. -/

namespace TimeTraps.Probability

open scoped NNReal

def observationDurationIndex (s : ℝ≥0) (d : List ℝ≥0) :
    Fin (observationDurations s d).length ≃ Fin d.length :=
  finCongr (observationDurations_length s d)

theorem observationDurationIndex_apply (s : ℝ≥0) (d : List ℝ≥0)
    (i : Fin (observationDurations s d).length) :
    (observationDurationIndex s d i).val = i.val := rfl

theorem elapsedObservationTime_recovery (s : ℝ≥0) (d : List ℝ≥0)
    (hs : ∀ t ∈ d, s ≤ t) (hd : d.Pairwise (· ≤ ·))
    (i : Fin (observationDurations s d).length) :
    elapsedObservationTime s (observationDurations s d) i =
      d.get (observationDurationIndex s d i) := by
  induction d generalizing s with
  | nil => exact Fin.elim0 i
  | cons t d ih =>
    have hst := hs t List.mem_cons_self
    obtain ⟨ht, hp⟩ := List.pairwise_cons.mp hd
    refine Fin.cases ?_ (fun j => ?_) i
    · change s + (t - s) = t
      exact add_tsub_cancel_of_le hst
    · change elapsedObservationTime (s + (t - s)) (observationDurations t d) j =
        d.get (observationDurationIndex t d j)
      rw [add_tsub_cancel_of_le hst]
      exact ih t ht hp j

end TimeTraps.Probability
