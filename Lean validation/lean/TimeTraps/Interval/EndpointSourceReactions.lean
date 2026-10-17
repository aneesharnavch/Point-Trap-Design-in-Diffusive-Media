module

public import TimeTraps.Interval.EndpointShares

@[expose] public section

/-! Divide all physical active strengths and the total budget by the
positive source mass. The architecture and absent endpoints are preserved. -/

namespace TimeTraps.Interval

open scoped BigOperators

variable {A : EndpointArchitecture} {K : ℝ}

noncomputable def EndpointReactions.normalize (R : EndpointReactions A K) (S : ℝ) (hS : 0 < S) :
    EndpointReactions A (K / S) where
  interiorStrength i := R.interiorStrength i / S
  leftStrength := R.leftStrength / S
  rightStrength := R.rightStrength / S
  interior_pos i := div_pos (R.interior_pos i) hS
  left_condition := by
    cases hl : A.leftReactive with
    | false => simp only [Bool.false_eq_true, if_false, R.left_zero hl, zero_div]
    | true => simp only [if_true]; exact div_pos (R.left_pos hl) hS
  right_condition := by
    cases hr : A.rightReactive with
    | false => simp only [Bool.false_eq_true, if_false, R.right_zero hr, zero_div]
    | true => simp only [if_true]; exact div_pos (R.right_pos hr) hS
  total_strength := by rw [← Finset.sum_div, ← add_div, ← add_div, R.total_strength]

theorem EndpointReactions.normalize_nodal (R : EndpointReactions A K) (S : ℝ) (hS : 0 < S)
    (v : Fin (A.interiorCount + 2)) : (R.normalize S hS).nodal v = R.nodal v / S := by
  refine Fin.cases rfl (fun j => ?_) v
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [nodal, normalize]
  · simp [nodal, normalize]

theorem EndpointReactions.normalize_activeStrength (R : EndpointReactions A K) (S : ℝ) (hS : 0 < S)
    (i : Fin A.count) : (R.normalize S hS).activeStrength i = R.activeStrength i / S :=
  R.normalize_nodal S hS (A.activeNode i)

end TimeTraps.Interval
