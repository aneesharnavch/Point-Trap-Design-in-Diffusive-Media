module

public import TimeTraps.Interval.StrictPartition
public import TimeTraps.Interval.CellSplitting
public import Mathlib.Topology.Order.Compact
public import Mathlib.Order.Fin.Basic

@[expose] public section

/-!
The compact closed simplex of ordered source partitions, with fixed cell
indices and possibly zero widths. Its topology is the inherited finite
product topology. Widths and balanced-cell barriers are continuous.
-/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

def closedPartitionSet (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {q | Monotone q ∧ q 0 = 0 ∧ q (Fin.last n) = 1}

abbrev ClosedPartition (n : ℕ) := {q // q ∈ closedPartitionSet n}

variable {n : ℕ}

def ClosedPartition.point (Q : ClosedPartition n) : Fin (n + 1) → ℝ := Q.val

theorem ClosedPartition.monotone (Q : ClosedPartition n) : Monotone Q.point := Q.property.1

theorem ClosedPartition.first (Q : ClosedPartition n) : Q.point 0 = 0 := Q.property.2.1

theorem ClosedPartition.last (Q : ClosedPartition n) : Q.point (Fin.last n) = 1 := Q.property.2.2

theorem ClosedPartition.size_pos (Q : ClosedPartition n) : 0 < n := by
  cases n with
  | zero =>
    have h : (0 : ℝ) = 1 := Q.first.symm.trans Q.last
    norm_num at h
  | succ n => omega

theorem ClosedPartition.point_mem (Q : ClosedPartition n) (e : Fin (n + 1)) :
    Q.point e ∈ Icc 0 1 := by
  rw [← Q.first, ← Q.last]
  exact ⟨Q.monotone (Fin.zero_le e), Q.monotone (Fin.le_last e)⟩

def ClosedPartition.width (Q : ClosedPartition n) (i : Fin n) : ℝ :=
  Q.point i.succ - Q.point i.castSucc

theorem ClosedPartition.width_nonneg (Q : ClosedPartition n) (i : Fin n) : 0 ≤ Q.width i :=
  sub_nonneg.mpr (Q.monotone (Fin.castSucc_le_succ i))

theorem ClosedPartition.width_sum (Q : ClosedPartition n) : (∑ i, Q.width i) = 1 := by
  unfold ClosedPartition.width
  rw [Finset.sum_sub_distrib]
  have h₀ := Fin.sum_univ_succ Q.point
  have h₁ := Fin.sum_univ_castSucc Q.point
  rw [Q.first] at h₀
  rw [Q.last] at h₁
  linarith

theorem ClosedPartition.positive_width (Q : ClosedPartition n) : ∃ i, 0 < Q.width i := by
  have hs : 0 < ∑ i, Q.width i := by rw [Q.width_sum]; norm_num
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => Q.width_nonneg i)).mp hs
  exact ⟨i, hi⟩

theorem ClosedPartition.strict_iff_width_pos (Q : ClosedPartition n) :
    StrictMono Q.point ↔ ∀ i, 0 < Q.width i := by
  rw [Fin.strictMono_iff_lt_succ]
  exact forall_congr' (fun i => sub_pos.symm)

def ClosedPartition.toStrict (Q : ClosedPartition n) (h : ∀ i, 0 < Q.width i) : StrictPartition n :=
  ⟨Q.point, Q.strict_iff_width_pos.mpr h, Q.first, Q.last⟩

def StrictPartition.closed (Q : StrictPartition n) : ClosedPartition n :=
  ⟨Q.point, Q.strictMono.monotone, Q.first, Q.last⟩

theorem StrictPartition.closed_width (Q : StrictPartition n) (i : Fin n) :
    Q.closed.width i = Q.width i := rfl

noncomputable def StrictPartition.uniform (n : ℕ) (hn : 0 < n) : StrictPartition n where
  point i := (i.val : ℝ) / n
  strictMono := by
    intro i j hij
    apply div_lt_div_of_pos_right
    · exact_mod_cast hij
    · exact_mod_cast hn
  first := by simp
  last := by
    change (n : ℝ) / n = 1
    exact div_self (by exact_mod_cast (Nat.ne_of_gt hn))

theorem closedPartition_nonempty (hn : 0 < n) : Nonempty (ClosedPartition n) :=
  ⟨(StrictPartition.uniform n hn).closed⟩

theorem closedPartitionSet_isClosed (n : ℕ) : IsClosed (closedPartitionSet n) :=
  isClosed_monotone.inter ((isClosed_eq (continuous_apply 0) continuous_const).inter
    (isClosed_eq (continuous_apply (Fin.last n)) continuous_const))

theorem closedPartitionSet_isCompact (n : ℕ) : IsCompact (closedPartitionSet n) := by
  apply (isCompact_univ_pi (fun _ : Fin (n + 1) => isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset
    (closedPartitionSet_isClosed n)
  intro q hq
  exact mem_pi.mpr (fun e _ => (show ClosedPartition n from ⟨q, hq⟩).point_mem e)

instance closedPartition_compactSpace (n : ℕ) : CompactSpace (ClosedPartition n) :=
  isCompact_iff_compactSpace.mp (closedPartitionSet_isCompact n)

theorem ClosedPartition.point_continuous (e : Fin (n + 1)) :
    Continuous (fun Q : ClosedPartition n => Q.point e) :=
  (continuous_apply e).comp continuous_subtype_val

theorem ClosedPartition.width_continuous (i : Fin n) :
    Continuous (fun Q : ClosedPartition n => Q.width i) :=
  (ClosedPartition.point_continuous i.succ).sub (ClosedPartition.point_continuous i.castSucc)

noncomputable def ClosedPartition.barrier (Q : ClosedPartition n) (W : CellWeight) (i : Fin n) : ℝ :=
  W.barrier (Q.point i.castSucc) (Q.point i.succ)

theorem ClosedPartition.barrier_nonneg (Q : ClosedPartition n) (W : CellWeight) (i : Fin n) :
    0 ≤ Q.barrier W i :=
  W.barrier_nonneg (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.monotone (Fin.castSucc_le_succ i))

theorem ClosedPartition.barrier_zero_of_width_zero (Q : ClosedPartition n) (W : CellWeight)
    (i : Fin n) (hi : Q.width i = 0) : Q.barrier W i = 0 := by
  have he : Q.point i.succ = Q.point i.castSucc := sub_eq_zero.mp hi
  change W.barrier _ _ = 0
  rw [he, W.barrier_diagonal]

theorem ClosedPartition.barrier_continuous (W : CellWeight) (i : Fin n) :
    Continuous (fun Q : ClosedPartition n => Q.barrier W i) :=
  W.barrier_continuous.comp_continuous
    ((ClosedPartition.point_continuous i.castSucc).prodMk (ClosedPartition.point_continuous i.succ))
    (fun Q => ⟨(Q.point_mem i.castSucc).1, Q.monotone (Fin.castSucc_le_succ i), (Q.point_mem i.succ).2⟩)

theorem StrictPartition.closed_barrier (Q : StrictPartition n) (W : CellWeight) (i : Fin n) :
    Q.closed.barrier W i = Q.barrier W i := rfl

end TimeTraps.Interval
