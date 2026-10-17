module

public import TimeTraps.Interval.EndpointArchitecture
public import TimeTraps.Interval.OrderedDesign

@[expose] public section

/-!
Physical reaction data for a fixed mixed architecture. Every interior
strength and every selected endpoint strength is positive; an absent
endpoint has strength zero. The nodal extension includes both physical
ends, also when there are no interior sites.
-/

namespace TimeTraps.Interval

open scoped BigOperators

structure EndpointReactions (A : EndpointArchitecture) (K : ℝ) where
  interiorStrength : Fin A.interiorCount → ℝ
  leftStrength : ℝ
  rightStrength : ℝ
  interior_pos : ∀ i, 0 < interiorStrength i
  left_condition : if A.leftReactive = true then 0 < leftStrength else leftStrength = 0
  right_condition : if A.rightReactive = true then 0 < rightStrength else rightStrength = 0
  total_strength : leftStrength + (∑ i, interiorStrength i) + rightStrength = K

variable {A : EndpointArchitecture} {K : ℝ}

theorem EndpointReactions.left_pos (R : EndpointReactions A K) (h : A.leftReactive = true) :
    0 < R.leftStrength := by simpa only [h, if_true] using R.left_condition

theorem EndpointReactions.right_pos (R : EndpointReactions A K) (h : A.rightReactive = true) :
    0 < R.rightStrength := by simpa only [h, if_true] using R.right_condition

theorem EndpointReactions.left_zero (R : EndpointReactions A K) (h : A.leftReactive = false) :
    R.leftStrength = 0 := by simpa only [h, Bool.false_eq_true, if_false] using R.left_condition

theorem EndpointReactions.right_zero (R : EndpointReactions A K) (h : A.rightReactive = false) :
    R.rightStrength = 0 := by simpa only [h, Bool.false_eq_true, if_false] using R.right_condition

theorem EndpointReactions.left_nonneg (R : EndpointReactions A K) : 0 ≤ R.leftStrength := by
  cases h : A.leftReactive with
  | false => rw [R.left_zero h]
  | true => exact (R.left_pos h).le

theorem EndpointReactions.right_nonneg (R : EndpointReactions A K) : 0 ≤ R.rightStrength := by
  cases h : A.rightReactive with
  | false => rw [R.right_zero h]
  | true => exact (R.right_pos h).le

def EndpointReactions.nodal (R : EndpointReactions A K) : Fin (A.interiorCount + 2) → ℝ :=
  Fin.cons R.leftStrength (Fin.snoc R.interiorStrength R.rightStrength)

theorem EndpointReactions.nodal_first (R : EndpointReactions A K) :
    R.nodal 0 = R.leftStrength := rfl

theorem EndpointReactions.nodal_last (R : EndpointReactions A K) :
    R.nodal (Fin.last (A.interiorCount + 1)) = R.rightStrength := by simp [nodal]

theorem EndpointReactions.nodal_interior (R : EndpointReactions A K)
    (i : Fin A.interiorCount) : R.nodal (trapNode i) = R.interiorStrength i := by
  simp [nodal, trapNode]

theorem EndpointReactions.nodal_nonneg (R : EndpointReactions A K) :
    ∀ v, 0 ≤ R.nodal v := by
  intro v
  refine Fin.cases R.left_nonneg (fun w => ?_) v
  refine Fin.lastCases ?_ (fun i => ?_) w
  · simpa [nodal] using R.right_nonneg
  · simpa [nodal] using (R.interior_pos i).le

theorem EndpointReactions.nodal_anchor (R : EndpointReactions A K) : ∃ v, 0 < R.nodal v := by
  by_cases hl : A.leftReactive = true
  · exact ⟨0, R.left_pos hl⟩
  by_cases hr : A.rightReactive = true
  · exact ⟨Fin.last (A.interiorCount + 1), by rw [R.nodal_last]; exact R.right_pos hr⟩
  have hm : 0 < A.interiorCount := by
    have ha := A.count_pos
    cases hleft : A.leftReactive <;> cases hright : A.rightReactive <;>
      simp_all [EndpointArchitecture.count]
  let i : Fin A.interiorCount := ⟨0, hm⟩
  exact ⟨trapNode i, by rw [R.nodal_interior]; exact R.interior_pos i⟩

theorem EndpointReactions.nodal_pairing (R : EndpointReactions A K)
    (U : Fin (A.interiorCount + 2) → ℝ) :
    (∑ v, R.nodal v * U v) = R.leftStrength * U 0 +
      (∑ i, R.interiorStrength i * U (trapNode i)) +
      R.rightStrength * U (Fin.last (A.interiorCount + 1)) := by
  rw [Fin.sum_univ_succ]
  simp only [nodal, Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_castSucc]
  simp [trapNode, add_assoc]

theorem EndpointReactions.nodal_sum (R : EndpointReactions A K) : (∑ v, R.nodal v) = K := by
  have hs : (∑ v, R.nodal v) = R.leftStrength +
      (∑ i, R.interiorStrength i) + R.rightStrength := by
    simpa only [mul_one] using R.nodal_pairing (fun _ => 1)
  exact hs.trans R.total_strength

theorem EndpointReactions.budget_pos (R : EndpointReactions A K) : 0 < K := by
  rw [← R.nodal_sum]
  obtain ⟨v, hv⟩ := R.nodal_anchor
  exact Finset.sum_pos' (fun w _ => R.nodal_nonneg w) ⟨v, Finset.mem_univ v, hv⟩

end TimeTraps.Interval
