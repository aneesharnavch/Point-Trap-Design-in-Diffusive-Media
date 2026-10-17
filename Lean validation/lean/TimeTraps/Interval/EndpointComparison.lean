module

public import TimeTraps.Interval.EndpointPartitionRoot
public import TimeTraps.Interval.PartitionComparison
public import TimeTraps.Interval.MediumUniformNorm

@[expose] public section

/-! Medium ordering and exact robustness for mixed endpoint/interior roots.
All comparisons keep the architecture and normalized budget fixed, including
closed grids with zero-width cells. -/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

theorem EndpointArchitecture.barrier_mono_weight (A : EndpointArchitecture) (Q : ClosedPartition A.count) (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x) (i : Fin A.count) :
    A.barrier Q W i ≤ A.barrier Q V i :=
  W.orientedBarrier_mono_weight V (A.kind i) hWV (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.monotone (Fin.castSucc_le_succ i))

theorem EndpointArchitecture.barrier_lt_weight_of_width_pos (A : EndpointArchitecture) (Q : ClosedPartition A.count) (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x) (i : Fin A.count)
    (hi : 0 < Q.width i) : A.barrier Q W i < A.barrier Q V i :=
  W.orientedBarrier_lt_weight V (A.kind i) hWV (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2 (sub_pos.mp hi)

theorem EndpointArchitecture.root_mono_weight (A : EndpointArchitecture) (Q : ClosedPartition A.count) (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x)
    {b : ℝ} (hb : 0 < b) : A.root Q W hb ≤ A.root Q V hb := by
  obtain ⟨i, hi⟩ := Q.positive_width
  exact budget_root_mono_barrier Finset.univ Q.width (A.barrier Q W) (A.barrier Q V)
    (fun j _ => Q.width_nonneg j) ⟨i, Finset.mem_univ i, hi⟩
    (fun j _ => A.barrier_mono_weight Q W V hWV j)
    (fun j _ => (A.root_spec Q V hb).1 j) (A.root_spec Q W hb).2 (A.root_spec Q V hb).2

theorem EndpointArchitecture.root_lt_weight (A : EndpointArchitecture) (Q : ClosedPartition A.count) (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x)
    {b : ℝ} (hb : 0 < b) : A.root Q W hb < A.root Q V hb := by
  obtain ⟨i, hi⟩ := Q.positive_width
  exact budget_root_lt_barrier Finset.univ Q.width (A.barrier Q W) (A.barrier Q V)
    (fun j _ => Q.width_nonneg j)
    (fun j _ => A.barrier_mono_weight Q W V (fun x hx => (hWV x hx).le) j)
    ⟨i, Finset.mem_univ i, hi, A.barrier_lt_weight_of_width_pos Q W V hWV i hi⟩
    (fun j _ => (A.root_spec Q V hb).1 j) (A.root_spec Q W hb).2 (A.root_spec Q V hb).2

theorem EndpointArchitecture.barrier_abs_sub_le (A : EndpointArchitecture) (Q : ClosedPartition A.count) (W V : CellWeight)
    {ε : ℝ} (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε) (i : Fin A.count) :
    |A.barrier Q W i - A.barrier Q V i| ≤ ε * Q.width i ^ 2 / 2 :=
  W.orientedBarrier_abs_sub_le V (A.kind i) hWV (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.monotone (Fin.castSucc_le_succ i))

theorem EndpointArchitecture.root_abs_sub_le_mesh (A : EndpointArchitecture) (Q : ClosedPartition A.count) (W V : CellWeight)
    {ε : ℝ} (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    {b : ℝ} (hb : 0 < b) : |A.root Q W hb - A.root Q V hb| ≤ ε * Q.mesh ^ 2 / 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hWV 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨i, hi⟩ := Q.positive_width
  apply budget_root_abs_sub_le Finset.univ Q.width (A.barrier Q W) (A.barrier Q V)
    (fun j _ => Q.width_nonneg j) ⟨i, Finset.mem_univ i, hi⟩ ?_
    (fun j _ => (A.root_spec Q W hb).1 j) (fun j _ => (A.root_spec Q V hb).1 j)
    (A.root_spec Q W hb).2 (A.root_spec Q V hb).2
  intro j _
  have hs : Q.width j ^ 2 ≤ Q.mesh ^ 2 :=
    (sq_le_sq₀ (Q.width_nonneg j) Q.mesh_pos.le).mpr (Q.width_le_mesh j)
  exact (A.barrier_abs_sub_le Q W V hWV j).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hε) (by norm_num))

theorem EndpointArchitecture.root_abs_sub_le (A : EndpointArchitecture) (Q : ClosedPartition A.count) (W V : CellWeight)
    {ε : ℝ} (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    {b : ℝ} (hb : 0 < b) : |A.root Q W hb - A.root Q V hb| ≤ ε / 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hWV 0 ⟨le_rfl, zero_le_one⟩)
  have hs : Q.mesh ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ Q.mesh_pos.le zero_le_one).mpr Q.mesh_le_one
  have hm := mul_le_mul_of_nonneg_left hs hε
  have h := A.root_abs_sub_le_mesh Q W V hWV hb
  nlinarith only [h, hm]

theorem EndpointArchitecture.root_abs_sub_le_Linfty (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W V : CellWeight)
    {ε : ℝ} (hWV : W.uniformDistance V ≤ ε) {b : ℝ} (hb : 0 < b) :
    |A.root Q W hb - A.root Q V hb| ≤ ε * Q.mesh ^ 2 / 2 :=
  A.root_abs_sub_le_mesh Q W V ((W.uniformDistance_le_iff V).mp hWV) hb

end TimeTraps.Interval
