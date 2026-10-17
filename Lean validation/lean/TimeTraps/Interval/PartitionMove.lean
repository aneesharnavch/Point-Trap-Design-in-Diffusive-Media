module

public import TimeTraps.Interval.ClosedPartition

@[expose] public section

/-!
Moving one internal partition boundary preserves every other cell. A closed
partition with both a zero and a positive width has adjacent cells of these
two types. This supplies an admissible split without changing the trap count.
-/

namespace TimeTraps.Interval

open Set

variable {n : ℕ}

theorem ClosedPartition.adjacent_zero_positive (Q : ClosedPartition (n + 1))
    (hz : ∃ k, Q.width k = 0) :
    ∃ i : Fin n, (Q.width i.castSucc = 0 ∧ 0 < Q.width i.succ) ∨
      (0 < Q.width i.castSucc ∧ Q.width i.succ = 0) := by
  by_contra hn
  have he : ∀ i : Fin n, Q.width i.castSucc = 0 ↔ Q.width i.succ = 0 := by
    intro i
    constructor
    · intro hi
      by_contra hj
      have hp : 0 < Q.width i.succ := lt_of_le_of_ne (Q.width_nonneg i.succ) (Ne.symm hj)
      exact hn ⟨i, Or.inl ⟨hi, hp⟩⟩
    · intro hi
      by_contra hj
      have hp : 0 < Q.width i.castSucc := lt_of_le_of_ne (Q.width_nonneg i.castSucc) (Ne.symm hj)
      exact hn ⟨i, Or.inr ⟨hp, hi⟩⟩
  have hall : ∀ k : Fin (n + 1), Q.width k = 0 ↔ Q.width 0 = 0 := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ i ih => exact (he i).symm.trans ih
  obtain ⟨j, hj⟩ := hz
  obtain ⟨k, hk⟩ := Q.positive_width
  exact (ne_of_gt hk) ((hall k).mpr ((hall j).mp hj))

def ClosedPartition.move (Q : ClosedPartition (n + 1)) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    ClosedPartition (n + 1) := by
  let m := i.castSucc.succ
  refine ⟨Function.update Q.point m c, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x = m
    · subst x
      rw [Function.update_self]
      by_cases hy : y = m
      · rw [hy, Function.update_self]
      · rw [Function.update_of_ne hy]
        have hr : i.succ.succ ≤ y := by
          have hn : y.val ≠ m.val := fun h => hy (Fin.ext h)
          change i.val + 1 + 1 ≤ y.val
          change i.val + 1 ≤ y.val at hxy
          dsimp [m] at hn
          omega
        exact hc.2.trans (Q.monotone hr)
    · rw [Function.update_of_ne hx]
      by_cases hy : y = m
      · subst y
        rw [Function.update_self]
        have hl : x ≤ i.castSucc.castSucc := by
          have hn : x.val ≠ m.val := fun h => hx (Fin.ext h)
          change x.val ≤ i.val
          change x.val ≤ i.val + 1 at hxy
          dsimp [m] at hn
          omega
        exact (Q.monotone hl).trans hc.1
      · rw [Function.update_of_ne hy]
        exact Q.monotone hxy
  · have he : (0 : Fin (n + 2)) ≠ m := by
      intro he
      have := congrArg Fin.val he
      dsimp [m] at this
      omega
    rw [Function.update_of_ne he]
    exact Q.first
  · have he : Fin.last (n + 1) ≠ m := by
      intro he
      have := congrArg Fin.val he
      dsimp [m] at this
      omega
    rw [Function.update_of_ne he]
    exact Q.last

theorem ClosedPartition.move_point (Q : ClosedPartition (n + 1)) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ))
    (e : Fin (n + 2)) :
    (Q.move i c hc).point e = if e = i.castSucc.succ then c else Q.point e :=
  Function.update_apply _ _ _ _

theorem ClosedPartition.move_middle (Q : ClosedPartition (n + 1)) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).point i.castSucc.succ = c := by rw [Q.move_point, if_pos rfl]

theorem ClosedPartition.move_other (Q : ClosedPartition (n + 1)) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ))
    (e : Fin (n + 2)) (he : e ≠ i.castSucc.succ) : (Q.move i c hc).point e = Q.point e := by
  rw [Q.move_point, if_neg he]

theorem ClosedPartition.move_left (Q : ClosedPartition (n + 1)) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).point i.castSucc.castSucc = Q.point i.castSucc.castSucc := by
  apply Q.move_other
  exact ne_of_lt (Fin.castSucc_lt_succ (i := i.castSucc))

theorem ClosedPartition.move_right (Q : ClosedPartition (n + 1)) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).point i.succ.succ = Q.point i.succ.succ := by
  apply Q.move_other
  intro he
  have := congrArg Fin.val he
  simp only [Fin.val_succ, Fin.val_castSucc] at this
  omega

theorem ClosedPartition.move_width_left (Q : ClosedPartition (n + 1)) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).width i.castSucc = c - Q.point i.castSucc.castSucc := by
  unfold ClosedPartition.width
  rw [Q.move_middle, Q.move_left]

theorem ClosedPartition.move_width_right (Q : ClosedPartition (n + 1)) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).width i.succ = Q.point i.succ.succ - c := by
  unfold ClosedPartition.width
  rw [← Fin.succ_castSucc, Q.move_right, Q.move_middle]

theorem ClosedPartition.move_barrier_left (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).barrier W i.castSucc = W.barrier (Q.point i.castSucc.castSucc) c := by
  unfold ClosedPartition.barrier
  rw [Q.move_middle, Q.move_left]

theorem ClosedPartition.move_barrier_right (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).barrier W i.succ = W.barrier c (Q.point i.succ.succ) := by
  unfold ClosedPartition.barrier
  rw [← Fin.succ_castSucc, Q.move_right, Q.move_middle]

theorem ClosedPartition.move_cell_other (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ))
    (k : Fin (n + 1)) (hl : k ≠ i.castSucc) (hr : k ≠ i.succ) :
    (Q.move i c hc).width k = Q.width k ∧ (Q.move i c hc).barrier W k = Q.barrier W k := by
  have h₀ : k.castSucc ≠ i.castSucc.succ := by
    intro he
    apply hr
    apply Fin.ext
    have := congrArg Fin.val he
    exact this
  have h₁ : k.succ ≠ i.castSucc.succ := fun he => hl (Fin.succ_injective _ he)
  unfold ClosedPartition.width ClosedPartition.barrier
  rw [Q.move_other i c hc _ h₀, Q.move_other i c hc _ h₁]
  exact ⟨rfl, rfl⟩

end TimeTraps.Interval
