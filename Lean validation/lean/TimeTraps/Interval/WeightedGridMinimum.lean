module

public import TimeTraps.Interval.WeightedGridMove

@[expose] public section

/-! Every minimizing weighted nearest-node grid is strict. Thus the compact
closed-grid minimum is attained by a grid with positive consecutive shares. -/

namespace TimeTraps.Interval

open Set

variable {n : ℕ}

theorem ClosedPartition.grid_improve_zero_cell (Q : ClosedPartition n) (W : CellWeight)
    (hz : ∃ i, Q.width i = 0) :
    ∃ P : ClosedPartition n, P.gridCost W < Q.gridCost W := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 Q.size_pos).elim
  | succ m =>
    obtain ⟨i, hi⟩ := Q.adjacent_zero_positive hz
    let α := Q.point i.castSucc.castSucc
    let β := Q.point i.succ.succ
    have hm : Q.point i.castSucc.succ = α ∨ Q.point i.castSucc.succ = β := by
      rcases hi with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact Or.inl (sub_eq_zero.mp hz)
      · apply Or.inr
        simpa only [ClosedPartition.width, Fin.succ_castSucc] using (sub_eq_zero.mp hz).symm
    have hab : α < β := by
      rcases hi with ⟨hz, hp⟩ | ⟨hp, hz⟩
      · have he : Q.point i.castSucc.succ = α := sub_eq_zero.mp hz
        have hp' := sub_pos.mp hp
        simpa only [ClosedPartition.width, ← Fin.succ_castSucc, he] using hp'
      · have he : Q.point i.castSucc.succ = β := by
          simpa only [ClosedPartition.width, Fin.succ_castSucc] using (sub_eq_zero.mp hz).symm
        have hp' := sub_pos.mp hp
        simpa only [he] using hp'
    have hc : (α + β) / 2 ∈ Ioo α β := by constructor <;> linarith
    exact ⟨Q.move i ((α + β) / 2) (Ioo_subset_Icc_self hc), Q.move_gridCost_lt W i hm hc⟩

theorem ClosedPartition.grid_minimizer_strict (Q : ClosedPartition n) (W : CellWeight)
    (hmin : ∀ P : ClosedPartition n, Q.gridCost W ≤ P.gridCost W) : StrictMono Q.point := by
  apply Q.strict_iff_width_pos.mpr
  intro i
  by_contra hn
  have hz : Q.width i = 0 := le_antisymm (le_of_not_gt hn) (Q.width_nonneg i)
  obtain ⟨P, hP⟩ := Q.grid_improve_zero_cell W ⟨i, hz⟩
  exact (not_lt_of_ge (hmin P)) hP

theorem StrictPartition.grid_minimum_exists (W : CellWeight) (hn : 0 < n) :
    ∃ Q : StrictPartition n, ∀ P : ClosedPartition n, Q.closed.gridCost W ≤ P.gridCost W := by
  obtain ⟨Q, hQ⟩ := ClosedPartition.grid_minimum_exists W hn
  have hs := Q.strict_iff_width_pos.mp (Q.grid_minimizer_strict W hQ)
  refine ⟨Q.toStrict hs, ?_⟩
  intro P
  have he : (Q.toStrict hs).closed = Q := Subtype.ext rfl
  rw [he]
  exact hQ P

theorem StrictPartition.grid_minimum_isLeast (W : CellWeight) (hn : 0 < n) :
    ∃ Q : StrictPartition n,
      IsLeast (range (fun P : ClosedPartition n => P.gridCost W)) (Q.closed.gridCost W) := by
  obtain ⟨Q, hQ⟩ := StrictPartition.grid_minimum_exists W hn
  refine ⟨Q, ⟨Q.closed, rfl⟩, ?_⟩
  rintro M ⟨P, rfl⟩
  exact hQ P

end TimeTraps.Interval
