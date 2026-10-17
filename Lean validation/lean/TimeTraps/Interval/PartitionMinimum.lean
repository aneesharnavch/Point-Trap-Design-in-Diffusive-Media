module

public import TimeTraps.Interval.PartitionRoot
public import TimeTraps.Interval.PartitionMove

@[expose] public section

/-!
Every minimizing closed partition is strict. A zero/positive adjacent pair
can be replaced by two positive children. Their barriers are both smaller
than the parent barrier, so the budget at the old root strictly decreases;
the new root is therefore strictly smaller.
-/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n : ℕ}

theorem sum_lt_of_pair {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (l r : ι) (hne : l ≠ r) (he : ∀ k, k ≠ l → k ≠ r → f k = g k)
    (hp : f l + f r < g l + g r) : (∑ k, f k) < ∑ k, g k := by
  have hs := Finset.sum_eq_add_of_mem (s := Finset.univ) (f := fun k => f k - g k)
    l r (Finset.mem_univ l) (Finset.mem_univ r) hne
    (fun k _ hk => sub_eq_zero.mpr (he k hk.1 hk.2))
  rw [Finset.sum_sub_distrib] at hs
  linarith

theorem ClosedPartition.move_decreases_root (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (i : Fin n)
    (hp : (Q.width i.castSucc = 0 ∧ 0 < Q.width i.succ) ∨
      (0 < Q.width i.castSucc ∧ Q.width i.succ = 0))
    {b : ℝ} (hb : 0 < b) :
    ∃ P : ClosedPartition (n + 1), P.root W hb < Q.root W hb := by
  let α := Q.point i.castSucc.castSucc
  let β := Q.point i.succ.succ
  let m := Q.point i.castSucc.succ
  let M := Q.root W hb
  let R := W.barrier α β
  have hwL : Q.width i.castSucc = m - α := rfl
  have hwR : Q.width i.succ = β - m := by
    unfold ClosedPartition.width
    rw [← Fin.succ_castSucc]
  have hrL : Q.barrier W i.castSucc = W.barrier α m := rfl
  have hrR : Q.barrier W i.succ = W.barrier m β := by
    unfold ClosedPartition.barrier
    rw [← Fin.succ_castSucc]
  have hbase : α < β ∧ R < M ∧
      Q.width i.castSucc / (M - Q.barrier W i.castSucc) +
      Q.width i.succ / (M - Q.barrier W i.succ) = (β - α) / (M - R) := by
    rcases hp with ⟨hz, hpos⟩ | ⟨hpos, hz⟩
    · have hm : m = α := sub_eq_zero.mp (hwL.symm.trans hz)
      have hab : α < β := by rw [hwR, hm] at hpos; exact sub_pos.mp hpos
      have hd := (Q.root_spec W hb).1 i.succ
      rw [hrR, hm] at hd
      refine ⟨hab, hd, ?_⟩
      rw [hwL, hwR, hrL, hrR, hm]
      simp only [sub_self, zero_div, zero_add]
      rfl
    · have hm : m = β := (sub_eq_zero.mp (hwR.symm.trans hz)).symm
      have hab : α < β := by rw [hwL, hm] at hpos; exact sub_pos.mp hpos
      have hd := (Q.root_spec W hb).1 i.castSucc
      rw [hrL, hm] at hd
      refine ⟨hab, hd, ?_⟩
      rw [hwL, hwR, hrL, hrR, hm]
      simp only [sub_self, zero_div, add_zero]
      rfl
  let c := (α + β) / 2
  have hc : c ∈ Ioo α β := by constructor <;> dsimp [c] <;> linarith [hbase.1]
  let P := Q.move i c (Ioo_subset_Icc_self hc)
  have hs := W.barrier_split (Q.point_mem i.castSucc.castSucc).1
    (Q.point_mem i.succ.succ).2 hc.1 hc.2
  have hdom : ∀ k, P.barrier W k < M := by
    intro k
    by_cases hl : k = i.castSucc
    · subst k
      change (Q.move i c _).barrier W i.castSucc < M
      rw [Q.move_barrier_left]
      exact hs.1.trans hbase.2.1
    · by_cases hr : k = i.succ
      · subst k
        change (Q.move i c _).barrier W i.succ < M
        rw [Q.move_barrier_right]
        exact hs.2.trans hbase.2.1
      · rw [(Q.move_cell_other W i c _ k hl hr).2]
        exact (Q.root_spec W hb).1 k
  have hpair : P.width i.castSucc / (M - P.barrier W i.castSucc) +
      P.width i.succ / (M - P.barrier W i.succ) <
      Q.width i.castSucc / (M - Q.barrier W i.castSucc) +
      Q.width i.succ / (M - Q.barrier W i.succ) := by
    calc
      _ = (c - α) / (M - W.barrier α c) + (β - c) / (M - W.barrier c β) := by
        change (Q.move i c _).width i.castSucc / (M - (Q.move i c _).barrier W i.castSucc) +
          (Q.move i c _).width i.succ / (M - (Q.move i c _).barrier W i.succ) = _
        rw [Q.move_width_left, Q.move_width_right, Q.move_barrier_left, Q.move_barrier_right]
      _ < (c - α) / (M - R) + (β - c) / (M - R) :=
        add_lt_add
          (div_lt_div_of_pos_left (sub_pos.mpr hc.1) (sub_pos.mpr hbase.2.1) (by linarith [hs.1]))
          (div_lt_div_of_pos_left (sub_pos.mpr hc.2) (sub_pos.mpr hbase.2.1) (by linarith [hs.2]))
      _ = (β - α) / (M - R) := by rw [← add_div]; congr 1; ring
      _ = _ := hbase.2.2.symm
  have hbudget : budget Finset.univ P.width (P.barrier W) M <
      budget Finset.univ Q.width (Q.barrier W) M := by
    apply sum_lt_of_pair _ _ i.castSucc i.succ (ne_of_lt Fin.castSucc_lt_succ) ?_ hpair
    intro k hl hr
    obtain ⟨hw, hR⟩ := Q.move_cell_other W i c (Ioo_subset_Icc_self hc) k hl hr
    rw [hw, hR]
  have hbudget' : budget Finset.univ P.width (P.barrier W) M < b := by
    exact hbudget.trans_eq (Q.root_spec W hb).2
  obtain ⟨j, hj⟩ := P.positive_width
  exact ⟨P, root_lt_of_budget_lt_nonneg Finset.univ P.width (P.barrier W)
    (fun k _ => P.width_nonneg k) ⟨j, Finset.mem_univ j, hj⟩
    (fun k _ => hdom k) (P.root_spec W hb).2 hbudget'⟩

theorem ClosedPartition.improve_zero_cell (Q : ClosedPartition n) (W : CellWeight)
    (hz : ∃ i, Q.width i = 0) {b : ℝ} (hb : 0 < b) :
    ∃ P : ClosedPartition n, P.root W hb < Q.root W hb := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 Q.size_pos).elim
  | succ m =>
    obtain ⟨i, hi⟩ := Q.adjacent_zero_positive hz
    exact Q.move_decreases_root W i hi hb

theorem ClosedPartition.minimizer_strict (Q : ClosedPartition n) (W : CellWeight)
    {b : ℝ} (hb : 0 < b) (hmin : ∀ P : ClosedPartition n, Q.root W hb ≤ P.root W hb) :
    StrictMono Q.point := by
  apply Q.strict_iff_width_pos.mpr
  intro i
  by_contra hn
  have hz : Q.width i = 0 := le_antisymm (le_of_not_gt hn) (Q.width_nonneg i)
  obtain ⟨P, hP⟩ := Q.improve_zero_cell W ⟨i, hz⟩ hb
  exact (not_lt_of_ge (hmin P)) hP

/-- The minimum on the closed simplex is attained by a strict partition,
and it is a least value among all closed and strict partitions. -/
theorem StrictPartition.minimum_exists (W : CellWeight) (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) :
    ∃ Q : StrictPartition n, ∀ P : ClosedPartition n, Q.closed.root W hb ≤ P.root W hb := by
  obtain ⟨Q, hQ⟩ := ClosedPartition.minimum_exists W hn hb
  have hs := Q.strict_iff_width_pos.mp (Q.minimizer_strict W hb hQ)
  refine ⟨Q.toStrict hs, ?_⟩
  intro P
  have he : (Q.toStrict hs).closed = Q := Subtype.ext rfl
  rw [he]
  exact hQ P

end TimeTraps.Interval
