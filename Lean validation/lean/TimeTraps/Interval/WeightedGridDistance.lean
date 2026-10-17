module

public import TimeTraps.Interval.ClosedPartition
public import Mathlib.Topology.Order.Lattice

@[expose] public section

/-! Exact distance to a finite grid, including repeated nodes. This is the
distance used in the independently defined weighted quantization objective. -/

namespace TimeTraps.Interval

open Set

variable {n : ℕ}

noncomputable def gridDistance (q : Fin (n + 1) → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => |x - q i|)

theorem gridDistance_nonneg (q : Fin (n + 1) → ℝ) (x : ℝ) : 0 ≤ gridDistance q x := by
  exact Finset.le_inf' _ _ (fun i _ => abs_nonneg (x - q i))

theorem gridDistance_le (q : Fin (n + 1) → ℝ) (x : ℝ) (i : Fin (n + 1)) :
    gridDistance q x ≤ |x - q i| :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem gridDistance_attained (q : Fin (n + 1) → ℝ) (x : ℝ) :
    ∃ i, gridDistance q x = |x - q i| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => |x - q i|)
  exact ⟨i, hi⟩

theorem gridDistance_at_node (q : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    gridDistance q (q i) = 0 := by
  have h := gridDistance_le q (q i) i
  simp only [sub_self, abs_zero] at h
  exact le_antisymm h (gridDistance_nonneg q _)

theorem gridDistance_continuous (q : Fin (n + 1) → ℝ) : Continuous (gridDistance q) := by
  exact Continuous.finset_inf'_apply _ (fun i _ => (continuous_id.sub continuous_const).abs)

theorem gridDistance_joint_continuous :
    Continuous (fun p : (Fin (n + 1) → ℝ) × ℝ => gridDistance p.1 p.2) := by
  exact Continuous.finset_inf'_apply _ (fun i _ =>
    (continuous_snd.sub ((continuous_apply i).comp continuous_fst)).abs)

theorem gridDistance_le_of_nodes {q r : Fin (n + 1) → ℝ} {δ : ℝ}
    (h : ∀ i, |q i - r i| ≤ δ) (x : ℝ) : gridDistance q x ≤ gridDistance r x + δ := by
  obtain ⟨i, hi⟩ := gridDistance_attained r x
  calc
    gridDistance q x ≤ |x - q i| := gridDistance_le q x i
    _ ≤ |x - r i| + |r i - q i| := abs_sub_le _ _ _
    _ ≤ gridDistance r x + δ := by rw [← hi, abs_sub_comm]; exact add_le_add le_rfl (h i)

theorem gridDistance_grid_lipschitz {q r : Fin (n + 1) → ℝ} {δ : ℝ}
    (h : ∀ i, |q i - r i| ≤ δ) (x : ℝ) : |gridDistance q x - gridDistance r x| ≤ δ := by
  have hqr := gridDistance_le_of_nodes h x
  have hrq := gridDistance_le_of_nodes (q := r) (r := q)
    (fun i => by simpa only [abs_sub_comm] using h i) x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem ClosedPartition.gridDistance_le_one (Q : ClosedPartition n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : gridDistance Q.point x ≤ 1 := by
  have h := gridDistance_le Q.point x 0
  rw [Q.first, sub_zero, abs_of_nonneg hx.1] at h
  exact h.trans hx.2

theorem ClosedPartition.gridDistance_square_lipschitz (Q R : ClosedPartition n) {δ x : ℝ}
    (h : ∀ i, |Q.point i - R.point i| ≤ δ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |gridDistance Q.point x ^ 2 - gridDistance R.point x ^ 2| ≤ 2 * δ := by
  have hd := gridDistance_grid_lipschitz h x
  have hQ := gridDistance_nonneg Q.point x
  have hR := gridDistance_nonneg R.point x
  have hQ1 := Q.gridDistance_le_one hx
  have hR1 := R.gridDistance_le_one hx
  have he : gridDistance Q.point x ^ 2 - gridDistance R.point x ^ 2 =
      (gridDistance Q.point x - gridDistance R.point x) *
        (gridDistance Q.point x + gridDistance R.point x) := by ring
  rw [he, abs_mul, abs_of_nonneg (add_nonneg hQ hR)]
  calc
    _ ≤ δ * (gridDistance Q.point x + gridDistance R.point x) :=
      mul_le_mul_of_nonneg_right hd (add_nonneg hQ hR)
    _ ≤ δ * 2 := mul_le_mul_of_nonneg_left (by linarith) ((abs_nonneg _).trans hd)
    _ = _ := by ring

end TimeTraps.Interval
