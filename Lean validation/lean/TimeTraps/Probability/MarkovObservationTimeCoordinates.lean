module

public import TimeTraps.Probability.MarkovObservationDurations

@[expose] public section

/-! Observation pruning preserves the literal cumulative observation
times. This identifies the previously proved kernel projections with
restriction to the retained time coordinates. -/

namespace TimeTraps.Probability

open scoped NNReal

variable {α : Type*}

def ElapsedObservationPruning.index {d e : List ℝ≥0}
    (p : ElapsedObservationPruning d e) : Fin e.length → Fin d.length :=
  match p with
  | .empty _ => Fin.elim0
  | .keep _ q => Fin.cons 0 (fun i => (q.index i).succ)
  | .merge _ _ _ _ q => fun i => (q.index i).succ
  | .trans p q => fun i => p.index (q.index i)

theorem ElapsedObservationPruning.stateMap_apply {d e : List ℝ≥0}
    (p : ElapsedObservationPruning d e) (q : Fin d.length → α) (i : Fin e.length) :
    p.stateMap q i = q (p.index i) := by
  induction p with
  | empty d => exact Fin.elim0 i
  | keep t p ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (Fin.tail q) j
  | merge s t d e p ih => exact ih (Fin.tail q) i
  | trans p r hp hr =>
    exact (hr (p.stateMap q) i).trans (hp q (r.index i))

def elapsedObservationTime : ℝ≥0 → (d : List ℝ≥0) → Fin d.length → ℝ≥0
  | _, [], i => Fin.elim0 i
  | s, t :: d, i => (Fin.cons (s + t) (elapsedObservationTime (s + t) d) :
      Fin (d.length + 1) → ℝ≥0) i

theorem ElapsedObservationPruning.time_coordinates {d e : List ℝ≥0}
    (p : ElapsedObservationPruning d e) (s : ℝ≥0) :
    p.stateMap (elapsedObservationTime s d) = elapsedObservationTime s e := by
  induction p generalizing s with
  | empty d => funext i; exact Fin.elim0 i
  | keep t p ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (s + t)) j
  | merge u v d e p ih =>
    change p.stateMap (Fin.cons (s + u + v) (elapsedObservationTime (s + u + v) d) :
      Fin (d.length + 1) → ℝ≥0) = _
    rw [add_assoc]
    exact ih s
  | trans p q hp hq =>
    change q.stateMap (p.stateMap (elapsedObservationTime s _)) = _
    rw [hp, hq]

end TimeTraps.Probability
