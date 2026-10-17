module

public import TimeTraps.Interval.ClosedPartition
public import TimeTraps.Interval.BudgetContinuity

@[expose] public section

/-!
The partition objective is the unique root of its independently defined
budget equation. It is continuous on the compact closed simplex, with the
paper's uniform bounds, and attains a minimum. Strictness of minimizers is
proved separately by a cell-splitting argument.
-/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n : ℕ}

theorem ClosedPartition.root_existsUnique (Q : ClosedPartition n) (W : CellWeight)
    {b : ℝ} (hb : 0 < b) :
    ∃! M : ℝ, (∀ i, Q.barrier W i < M) ∧ budget Finset.univ Q.width (Q.barrier W) M = b := by
  obtain ⟨i, hi⟩ := Q.positive_width
  simpa only [Finset.mem_univ, forall_const] using
    budget_root_existsUnique_nonneg Finset.univ Q.width (Q.barrier W)
      (fun i _ => Q.width_nonneg i) ⟨i, Finset.mem_univ i, hi⟩
      (fun i _ => Q.barrier_nonneg W i) (fun i _ => Q.barrier_zero_of_width_zero W i) hb

noncomputable def ClosedPartition.root (Q : ClosedPartition n) (W : CellWeight)
    {b : ℝ} (hb : 0 < b) : ℝ := Classical.choose (Q.root_existsUnique W hb)

theorem ClosedPartition.root_spec (Q : ClosedPartition n) (W : CellWeight)
    {b : ℝ} (hb : 0 < b) :
    (∀ i, Q.barrier W i < Q.root W hb) ∧
      budget Finset.univ Q.width (Q.barrier W) (Q.root W hb) = b :=
  (Classical.choose_spec (Q.root_existsUnique W hb)).1

theorem ClosedPartition.eq_root (Q : ClosedPartition n) (W : CellWeight)
    {b M : ℝ} (hb : 0 < b) (hM : ∀ i, Q.barrier W i < M)
    (hroot : budget Finset.univ Q.width (Q.barrier W) M = b) : M = Q.root W hb :=
  (Classical.choose_spec (Q.root_existsUnique W hb)).2 M ⟨hM, hroot⟩

theorem ClosedPartition.root_pos (Q : ClosedPartition n) (W : CellWeight)
    {b : ℝ} (hb : 0 < b) : 0 < Q.root W hb := by
  obtain ⟨i, _⟩ := Q.positive_width
  exact (Q.barrier_nonneg W i).trans_lt ((Q.root_spec W hb).1 i)

theorem ClosedPartition.root_lower (Q : ClosedPartition n) (W : CellWeight)
    {b : ℝ} (hb : 0 < b) : 1 / b ≤ Q.root W hb := by
  obtain ⟨i, hi⟩ := Q.positive_width
  have h := budget_root_lower_nonneg Finset.univ Q.width (Q.barrier W)
    (fun i _ => Q.width_nonneg i) ⟨i, Finset.mem_univ i, hi⟩ (fun i _ => Q.barrier_nonneg W i)
    hb (fun i _ => (Q.root_spec W hb).1 i) (Q.root_spec W hb).2
  simpa only [Q.width_sum] using h

theorem ClosedPartition.root_upper (Q : ClosedPartition n) (W : CellWeight)
    {b Rmax : ℝ} (hb : 0 < b) (hR : ∀ i, Q.barrier W i ≤ Rmax) :
    Q.root W hb ≤ Rmax + 1 / b := by
  obtain ⟨i, hi⟩ := Q.positive_width
  have h := budget_root_upper_nonneg Finset.univ Q.width (Q.barrier W)
    (fun i _ => Q.width_nonneg i) ⟨i, Finset.mem_univ i, hi⟩ hb (fun i _ => hR i)
    (Q.root_spec W hb).2
  simpa only [Q.width_sum] using h

theorem ClosedPartition.root_continuous (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    Continuous (fun Q : ClosedPartition n => Q.root W hb) := by
  apply continuous_iff_continuousAt.mpr
  intro Q
  have hpos : ∀ P : ClosedPartition n, ∃ i ∈ Finset.univ, 0 < P.width i := by
    intro P
    obtain ⟨i, hi⟩ := P.positive_width
    exact ⟨i, Finset.mem_univ i, hi⟩
  exact budget_root_continuousAt Finset.univ (fun P : ClosedPartition n => P.width)
    (fun P => P.barrier W) (fun P => P.root W hb)
    (fun P i _ => P.width_nonneg i) hpos
    (fun P i _ => (P.root_spec W hb).1 i) (fun P => (P.root_spec W hb).2)
    (fun i _ => (ClosedPartition.width_continuous i).continuousAt)
    (fun i _ => (ClosedPartition.barrier_continuous W i).continuousAt)

/-- Compactness supplies an actual partition and a least value, not only
an equality between infima. -/
theorem ClosedPartition.minimum_exists (W : CellWeight) (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) :
    ∃ Q : ClosedPartition n, ∀ P : ClosedPartition n, Q.root W hb ≤ P.root W hb := by
  obtain ⟨Q, _, hQ⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set (ClosedPartition n)).Nonempty from
      ⟨(StrictPartition.uniform n hn).closed, mem_univ _⟩)
    (ClosedPartition.root_continuous W hb).continuousOn
  exact ⟨Q, fun P => hQ (mem_univ P)⟩

theorem ClosedPartition.minimum_isLeast (W : CellWeight) (hn : 0 < n)
    {b : ℝ} (hb : 0 < b) :
    ∃ Q : ClosedPartition n, IsLeast (range (fun P : ClosedPartition n => P.root W hb)) (Q.root W hb) := by
  obtain ⟨Q, hQ⟩ := ClosedPartition.minimum_exists W hn hb
  refine ⟨Q, ⟨Q, rfl⟩, ?_⟩
  rintro M ⟨P, rfl⟩
  exact hQ P

end TimeTraps.Interval
