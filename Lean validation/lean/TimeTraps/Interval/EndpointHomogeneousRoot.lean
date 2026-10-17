module

public import TimeTraps.Interval.EndpointHomogeneousPartition

@[expose] public section

/-! The exact homogeneous mixed root and its unique equality partition.
The proof combines the arithmetic-harmonic bound with the weighted cubic
identity, including zero-width trial partitions. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

theorem EndpointArchitecture.constant_root_moment_bound (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {C b : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    1 / b + C / 2 * (∑ i, Q.width i ^ 3 / A.sideCount i ^ 2) ≤ A.root Q W hb := by
  have h := (budget_root_mean_barrier_bound Finset.univ Q.width (A.barrier Q W)
    (fun i _ => Q.width_nonneg i) Q.width_sum hb (fun i _ => (A.root_spec Q W hb).1 i)
    (A.root_spec Q W hb).2).1
  have hs : (∑ i, Q.width i * A.barrier Q W i) = C / 2 * ∑ i, Q.width i ^ 3 / A.sideCount i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [A.barrier_constant Q W hC i]
    ring
  rwa [hs] at h

theorem EndpointArchitecture.constant_root_lower (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {C b : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    1 / b + C / (2 * A.sideTotal ^ 2) ≤ A.root Q W hb := by
  have hCp : 0 < C := by rw [← hC 0 ⟨le_rfl, zero_le_one⟩]; exact W.positive 0 ⟨le_rfl, zero_le_one⟩
  calc
    _ = 1 / b + C / 2 * (1 / A.sideTotal ^ 2) := by ring
    _ ≤ 1 / b + C / 2 * ∑ i, Q.width i ^ 3 / A.sideCount i ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left (A.cubic_width_bound Q).1 (show 0 ≤ C / 2 by positivity)
      linarith
    _ ≤ A.root Q W hb := A.constant_root_moment_bound Q W hC hb

theorem EndpointArchitecture.homogeneousPartition_barrier (A : EndpointArchitecture)
    (W : CellWeight) {C : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (i : Fin A.count) :
    A.barrier A.homogeneousPartition.closed W i = C / (2 * A.sideTotal ^ 2) := by
  rw [A.barrier_constant _ W hC i, A.homogeneousPartition_width]
  unfold homogeneousShare
  field_simp [ne_of_gt (A.sideCount_pos i), ne_of_gt A.sideTotal_pos]

theorem EndpointArchitecture.homogeneousPartition_root (A : EndpointArchitecture)
    (W : CellWeight) {C b : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    A.root A.homogeneousPartition.closed W hb = 1 / b + C / (2 * A.sideTotal ^ 2) := by
  apply (A.eq_root A.homogeneousPartition.closed W hb ?_ ?_).symm
  · intro i
    rw [A.homogeneousPartition_barrier W hC i]
    linarith [one_div_pos.mpr hb]
  · unfold budget
    simp_rw [A.homogeneousPartition_barrier W hC]
    have he : 1 / b + C / (2 * A.sideTotal ^ 2) - C / (2 * A.sideTotal ^ 2) = 1 / b := by ring
    rw [he, ← Finset.sum_div, A.homogeneousPartition.closed.width_sum]
    field_simp [ne_of_gt hb]

theorem EndpointArchitecture.constant_root_eq_iff_width (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {C b : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    A.root Q W hb = 1 / b + C / (2 * A.sideTotal ^ 2) ↔ ∀ i, Q.width i = A.homogeneousShare i := by
  constructor
  · intro he
    have hCp : 0 < C := by rw [← hC 0 ⟨le_rfl, zero_le_one⟩]; exact W.positive 0 ⟨le_rfl, zero_le_one⟩
    have hm := A.constant_root_moment_bound Q W hC hb
    rw [he, show C / (2 * A.sideTotal ^ 2) = C / 2 * (1 / A.sideTotal ^ 2) by ring] at hm
    have hu : (∑ i, Q.width i ^ 3 / A.sideCount i ^ 2) ≤ 1 / A.sideTotal ^ 2 :=
      le_of_mul_le_mul_left (show C / 2 * (∑ i, Q.width i ^ 3 / A.sideCount i ^ 2) ≤
        C / 2 * (1 / A.sideTotal ^ 2) by linarith) (by positivity)
    exact (A.cubic_width_bound Q).2.mp (le_antisymm hu (A.cubic_width_bound Q).1)
  · intro hw
    rw [A.homogeneousPartition_unique Q hw]
    exact A.homogeneousPartition_root W hC hb

theorem EndpointArchitecture.constant_minimizer_iff (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {C b : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    (∀ P : ClosedPartition A.count, A.root Q W hb ≤ A.root P W hb) ↔
      Q = A.homogeneousPartition.closed := by
  constructor
  · intro hmin
    have hu := hmin A.homogeneousPartition.closed
    rw [A.homogeneousPartition_root W hC hb] at hu
    have he := le_antisymm hu (A.constant_root_lower Q W hC hb)
    exact A.homogeneousPartition_unique Q ((A.constant_root_eq_iff_width Q W hC hb).mp he)
  · rintro rfl P
    rw [A.homogeneousPartition_root W hC hb]
    exact A.constant_root_lower P W hC hb

end TimeTraps.Interval
