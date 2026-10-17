module

public import TimeTraps.Interval.CellPerturbation
public import TimeTraps.Interval.BudgetComparison
public import TimeTraps.Interval.PartitionRoot

@[expose] public section

/-!
Medium comparison for the genuine partition roots at a common normalized
budget. The mesh is the maximum of the actual source-cell widths, including
zero cells on the closed simplex. The stated robustness constant is
ε mesh² / 2.
-/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

variable {n : ℕ}

noncomputable def ClosedPartition.mesh (Q : ClosedPartition n) : ℝ :=
  Finset.univ.sup' ⟨⟨0, Q.size_pos⟩, Finset.mem_univ _⟩ Q.width

theorem ClosedPartition.width_le_mesh (Q : ClosedPartition n) (i : Fin n) : Q.width i ≤ Q.mesh :=
  Finset.le_sup' Q.width (Finset.mem_univ i)

theorem ClosedPartition.mesh_pos (Q : ClosedPartition n) : 0 < Q.mesh := by
  obtain ⟨i, hi⟩ := Q.positive_width
  exact hi.trans_le (Q.width_le_mesh i)

theorem ClosedPartition.width_le_one (Q : ClosedPartition n) (i : Fin n) : Q.width i ≤ 1 := by
  unfold width
  linarith [(Q.point_mem i.castSucc).1, (Q.point_mem i.succ).2]

theorem ClosedPartition.mesh_le_one (Q : ClosedPartition n) : Q.mesh ≤ 1 :=
  Finset.sup'_le _ _ (fun i _ => Q.width_le_one i)

theorem ClosedPartition.barrier_mono_weight (Q : ClosedPartition n) (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x) (i : Fin n) :
    Q.barrier W i ≤ Q.barrier V i :=
  W.barrier_mono_weight V hWV (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.monotone (Fin.castSucc_le_succ i))

theorem ClosedPartition.barrier_lt_weight_of_width_pos (Q : ClosedPartition n) (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x) (i : Fin n)
    (hi : 0 < Q.width i) : Q.barrier W i < Q.barrier V i :=
  W.barrier_lt_weight V hWV (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2 (sub_pos.mp hi)

theorem ClosedPartition.root_mono_weight (Q : ClosedPartition n) (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x)
    {b : ℝ} (hb : 0 < b) : Q.root W hb ≤ Q.root V hb := by
  obtain ⟨i, hi⟩ := Q.positive_width
  exact budget_root_mono_barrier Finset.univ Q.width (Q.barrier W) (Q.barrier V)
    (fun j _ => Q.width_nonneg j) ⟨i, Finset.mem_univ i, hi⟩
    (fun j _ => Q.barrier_mono_weight W V hWV j)
    (fun j _ => (Q.root_spec V hb).1 j) (Q.root_spec W hb).2 (Q.root_spec V hb).2

theorem ClosedPartition.root_lt_weight (Q : ClosedPartition n) (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x)
    {b : ℝ} (hb : 0 < b) : Q.root W hb < Q.root V hb := by
  obtain ⟨i, hi⟩ := Q.positive_width
  exact budget_root_lt_barrier Finset.univ Q.width (Q.barrier W) (Q.barrier V)
    (fun j _ => Q.width_nonneg j)
    (fun j _ => Q.barrier_mono_weight W V (fun x hx => (hWV x hx).le) j)
    ⟨i, Finset.mem_univ i, hi, Q.barrier_lt_weight_of_width_pos W V hWV i hi⟩
    (fun j _ => (Q.root_spec V hb).1 j) (Q.root_spec W hb).2 (Q.root_spec V hb).2

theorem ClosedPartition.barrier_abs_sub_le (Q : ClosedPartition n) (W V : CellWeight)
    {ε : ℝ} (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε) (i : Fin n) :
    |Q.barrier W i - Q.barrier V i| ≤ ε * Q.width i ^ 2 / 2 :=
  W.barrier_abs_sub_le V hWV (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.monotone (Fin.castSucc_le_succ i))

theorem ClosedPartition.root_abs_sub_le_mesh (Q : ClosedPartition n) (W V : CellWeight)
    {ε : ℝ} (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    {b : ℝ} (hb : 0 < b) : |Q.root W hb - Q.root V hb| ≤ ε * Q.mesh ^ 2 / 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hWV 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨i, hi⟩ := Q.positive_width
  apply budget_root_abs_sub_le Finset.univ Q.width (Q.barrier W) (Q.barrier V)
    (fun j _ => Q.width_nonneg j) ⟨i, Finset.mem_univ i, hi⟩ ?_
    (fun j _ => (Q.root_spec W hb).1 j) (fun j _ => (Q.root_spec V hb).1 j)
    (Q.root_spec W hb).2 (Q.root_spec V hb).2
  intro j _
  have hs : Q.width j ^ 2 ≤ Q.mesh ^ 2 :=
    (sq_le_sq₀ (Q.width_nonneg j) Q.mesh_pos.le).mpr (Q.width_le_mesh j)
  exact (Q.barrier_abs_sub_le W V hWV j).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hε) (by norm_num))

theorem ClosedPartition.root_abs_sub_le (Q : ClosedPartition n) (W V : CellWeight)
    {ε : ℝ} (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    {b : ℝ} (hb : 0 < b) : |Q.root W hb - Q.root V hb| ≤ ε / 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hWV 0 ⟨le_rfl, zero_le_one⟩)
  have hs : Q.mesh ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ Q.mesh_pos.le zero_le_one).mpr Q.mesh_le_one
  have hm := mul_le_mul_of_nonneg_left hs hε
  have h := Q.root_abs_sub_le_mesh W V hWV hb
  nlinarith only [h, hm]

end TimeTraps.Interval
