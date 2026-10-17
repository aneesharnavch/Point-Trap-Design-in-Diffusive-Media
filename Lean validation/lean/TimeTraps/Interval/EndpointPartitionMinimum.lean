module

public import TimeTraps.Interval.EndpointPartitionMove
public import TimeTraps.Interval.PartitionMinimum

@[expose] public section

/-!
Every closed mixed-cell minimizer has positive widths. A small transfer to
a zero cell preserves the assigned kinds and all other cells. Both new
barriers lie below the old donor barrier, which strictly lowers the budget
at the old root and hence strictly lowers the actual scalar root.
-/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n : ℕ}

theorem ClosedPartition.mixed_move_decreases_budget (Q : ClosedPartition (n + 1))
    (W : CellWeight) (kind : Fin (n + 1) → CellKind) (i : Fin n)
    (hp : (Q.width i.castSucc = 0 ∧ 0 < Q.width i.succ) ∨
      (0 < Q.width i.castSucc ∧ Q.width i.succ = 0))
    {M : ℝ} (hM : ∀ k, Q.mixedBarrier W kind k < M) :
    ∃ P : ClosedPartition (n + 1), (∀ k, P.mixedBarrier W kind k < M) ∧
      budget Finset.univ P.width (P.mixedBarrier W kind) M <
        budget Finset.univ Q.width (Q.mixedBarrier W kind) M := by
  let α := Q.point i.castSucc.castSucc
  let β := Q.point i.succ.succ
  let m := Q.point i.castSucc.succ
  have hwL : Q.width i.castSucc = m - α := rfl
  have hwR : Q.width i.succ = β - m := by
    unfold ClosedPartition.width
    rw [← Fin.succ_castSucc]
  have hrL : Q.mixedBarrier W kind i.castSucc = W.orientedBarrier (kind i.castSucc) α m := rfl
  have hrR : Q.mixedBarrier W kind i.succ = W.orientedBarrier (kind i.succ) m β := by
    unfold ClosedPartition.mixedBarrier
    rw [← Fin.succ_castSucc]
  have hbase : ∃ R c, c ∈ Ioo α β ∧ R < M ∧
      W.orientedBarrier (kind i.castSucc) α c < R ∧
      W.orientedBarrier (kind i.succ) c β < R ∧
      Q.width i.castSucc / (M - Q.mixedBarrier W kind i.castSucc) +
        Q.width i.succ / (M - Q.mixedBarrier W kind i.succ) = (β - α) / (M - R) := by
    rcases hp with ⟨hz, hpos⟩ | ⟨hpos, hz⟩
    · have hm : m = α := sub_eq_zero.mp (hwL.symm.trans hz)
      have hab : α < β := by rw [hwR, hm] at hpos; exact sub_pos.mp hpos
      have hd := hM i.succ
      rw [hrR, hm] at hd
      obtain ⟨c, hc, hcL, hcR⟩ := W.oriented_split_left_exists
        (kind i.castSucc) (kind i.succ) (Q.point_mem i.castSucc.castSucc).1
        (Q.point_mem i.succ.succ).2 hab
      refine ⟨W.orientedBarrier (kind i.succ) α β, c, hc, hd, hcL, hcR, ?_⟩
      rw [hwL, hwR, hrL, hrR, hm]
      simp only [sub_self, zero_div, zero_add]
    · have hm : m = β := (sub_eq_zero.mp (hwR.symm.trans hz)).symm
      have hab : α < β := by rw [hwL, hm] at hpos; exact sub_pos.mp hpos
      have hd := hM i.castSucc
      rw [hrL, hm] at hd
      obtain ⟨c, hc, hcL, hcR⟩ := W.oriented_split_right_exists
        (kind i.castSucc) (kind i.succ) (Q.point_mem i.castSucc.castSucc).1
        (Q.point_mem i.succ.succ).2 hab
      refine ⟨W.orientedBarrier (kind i.castSucc) α β, c, hc, hd, hcL, hcR, ?_⟩
      rw [hwL, hwR, hrL, hrR, hm]
      simp only [sub_self, zero_div, add_zero]
  obtain ⟨R, c, hc, hRM, hRcL, hRcR, hpair_old⟩ := hbase
  let P := Q.move i c (Ioo_subset_Icc_self hc)
  have hdom : ∀ k, P.mixedBarrier W kind k < M := by
    intro k
    by_cases hl : k = i.castSucc
    · subst k
      change (Q.move i c _).mixedBarrier W kind i.castSucc < M
      rw [Q.move_mixedBarrier_left]
      exact hRcL.trans hRM
    · by_cases hr : k = i.succ
      · subst k
        change (Q.move i c _).mixedBarrier W kind i.succ < M
        rw [Q.move_mixedBarrier_right]
        exact hRcR.trans hRM
      · rw [(Q.move_mixedCell_other W kind i c _ k hl hr).2]
        exact hM k
  have hpair : P.width i.castSucc / (M - P.mixedBarrier W kind i.castSucc) +
      P.width i.succ / (M - P.mixedBarrier W kind i.succ) <
      Q.width i.castSucc / (M - Q.mixedBarrier W kind i.castSucc) +
      Q.width i.succ / (M - Q.mixedBarrier W kind i.succ) := by
    calc
      _ = (c - α) / (M - W.orientedBarrier (kind i.castSucc) α c) +
          (β - c) / (M - W.orientedBarrier (kind i.succ) c β) := by
        change (Q.move i c _).width i.castSucc /
          (M - (Q.move i c _).mixedBarrier W kind i.castSucc) +
          (Q.move i c _).width i.succ / (M - (Q.move i c _).mixedBarrier W kind i.succ) = _
        rw [Q.move_width_left, Q.move_width_right,
          Q.move_mixedBarrier_left, Q.move_mixedBarrier_right]
      _ < (c - α) / (M - R) + (β - c) / (M - R) :=
        add_lt_add
          (div_lt_div_of_pos_left (sub_pos.mpr hc.1) (sub_pos.mpr hRM) (by linarith))
          (div_lt_div_of_pos_left (sub_pos.mpr hc.2) (sub_pos.mpr hRM) (by linarith))
      _ = (β - α) / (M - R) := by rw [← add_div]; congr 1; ring
      _ = _ := hpair_old.symm
  refine ⟨P, hdom, ?_⟩
  apply sum_lt_of_pair _ _ i.castSucc i.succ (ne_of_lt Fin.castSucc_lt_succ) ?_ hpair
  intro k hl hr
  obtain ⟨hw, hR⟩ := Q.move_mixedCell_other W kind i c (Ioo_subset_Icc_self hc) k hl hr
  rw [hw, hR]

theorem ClosedPartition.mixed_improve_zero_cell (Q : ClosedPartition n)
    (W : CellWeight) (kind : Fin n → CellKind) (hz : ∃ i, Q.width i = 0)
    {M : ℝ} (hM : ∀ i, Q.mixedBarrier W kind i < M) :
    ∃ P : ClosedPartition n, (∀ i, P.mixedBarrier W kind i < M) ∧
      budget Finset.univ P.width (P.mixedBarrier W kind) M <
        budget Finset.univ Q.width (Q.mixedBarrier W kind) M := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 Q.size_pos).elim
  | succ n =>
    obtain ⟨i, hi⟩ := Q.adjacent_zero_positive hz
    exact Q.mixed_move_decreases_budget W kind i hi hM

theorem EndpointArchitecture.improve_zero_cell (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) (hz : ∃ i, Q.width i = 0)
    {b : ℝ} (hb : 0 < b) :
    ∃ P : ClosedPartition A.count, A.root P W hb < A.root Q W hb := by
  obtain ⟨P, hPM, hbudget⟩ := Q.mixed_improve_zero_cell W A.kind hz (A.root_spec Q W hb).1
  have hbudget' : budget Finset.univ P.width (A.barrier P W) (A.root Q W hb) < b :=
    hbudget.trans_eq (A.root_spec Q W hb).2
  obtain ⟨j, hj⟩ := P.positive_width
  exact ⟨P, root_lt_of_budget_lt_nonneg Finset.univ P.width (A.barrier P W)
    (fun k _ => P.width_nonneg k) ⟨j, Finset.mem_univ j, hj⟩
    (fun k _ => hPM k) (A.root_spec P W hb).2 hbudget'⟩

theorem EndpointArchitecture.minimizer_strict (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {b : ℝ} (hb : 0 < b)
    (hmin : ∀ P : ClosedPartition A.count, A.root Q W hb ≤ A.root P W hb) :
    StrictMono Q.point := by
  apply Q.strict_iff_width_pos.mpr
  intro i
  by_contra hn
  have hz : Q.width i = 0 := le_antisymm (le_of_not_gt hn) (Q.width_nonneg i)
  obtain ⟨P, hP⟩ := A.improve_zero_cell Q W ⟨i, hz⟩ hb
  exact (not_lt_of_ge (hmin P)) hP

theorem EndpointArchitecture.strict_minimum_exists (A : EndpointArchitecture)
    (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    ∃ Q : StrictPartition A.count, ∀ P : ClosedPartition A.count,
      A.root Q.closed W hb ≤ A.root P W hb := by
  obtain ⟨Q, hQ⟩ := A.minimum_exists W hb
  have hs := Q.strict_iff_width_pos.mp (A.minimizer_strict Q W hb hQ)
  refine ⟨Q.toStrict hs, ?_⟩
  intro P
  have he : (Q.toStrict hs).closed = Q := Subtype.ext rfl
  rw [he]
  exact hQ P

theorem EndpointArchitecture.strict_minimum_isLeast (A : EndpointArchitecture)
    (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    ∃ Q : StrictPartition A.count,
      IsLeast (range (fun P : StrictPartition A.count => A.root P.closed W hb))
        (A.root Q.closed W hb) := by
  obtain ⟨Q, hQ⟩ := A.strict_minimum_exists W hb
  refine ⟨Q, ⟨Q, rfl⟩, ?_⟩
  rintro M ⟨P, rfl⟩
  exact hQ P.closed

end TimeTraps.Interval
