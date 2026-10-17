module

public import TimeTraps.Interval.ConstantCell
public import TimeTraps.Interval.UniformPartition
public import TimeTraps.Interval.PartitionRoot
public import TimeTraps.Interval.BudgetMoment
public import TimeTraps.Analysis.CubicMoment

@[expose] public section

/-!
The exact constant-weight partition optimum and unique equality partition.
The lower bound combines the root's arithmetic--harmonic inequality with
the exact cubic-width inequality. No optimization search is used.
-/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

theorem StrictPartition.uniform_center_constant (W : CellWeight) (hn : 0 < n)
    {C : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (i : Fin n) :
    (StrictPartition.uniform n hn).center W i = (2 * (i.val : ℝ) + 1) / (2 * n) := by
  let Q := StrictPartition.uniform n hn
  change W.center (Q.point i.castSucc) (Q.point i.succ) = _
  rw [W.center_constant hC (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.strictMono.monotone (Fin.castSucc_le_succ i))]
  change ((i.val : ℝ) / n + ((i.val + 1 : ℕ) : ℝ) / n) / 2 = _
  rw [Nat.cast_add, Nat.cast_one]
  ring

theorem ClosedPartition.barrier_constant (Q : ClosedPartition n) (W : CellWeight) {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (i : Fin n) :
    Q.barrier W i = C * Q.width i ^ 2 / 8 :=
  W.barrier_constant hC (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.monotone (Fin.castSucc_le_succ i))

theorem ClosedPartition.cubic_width_bound (Q : ClosedPartition n) :
    1 / (n : ℝ) ^ 2 ≤ (∑ i, Q.width i ^ 3) ∧
      ((∑ i, Q.width i ^ 3) = 1 / (n : ℝ) ^ 2 ↔ ∀ i, Q.width i = 1 / (n : ℝ)) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Q.size_pos
  have h := weighted_cubic_bound Finset.univ (fun _ : Fin n => (1 : ℝ)) Q.width
    hn (by norm_num : (0 : ℝ) < 1) (by simp) (by simpa only [one_mul] using Q.width_sum)
    (fun _ _ => by norm_num) (fun i _ => Q.width_nonneg i)
  simpa only [one_pow, one_mul, Finset.mem_univ, forall_const] using h

theorem ClosedPartition.constant_root_moment_bound (Q : ClosedPartition n) (W : CellWeight)
    {C b : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    1 / b + C / 8 * (∑ i, Q.width i ^ 3) ≤ Q.root W hb := by
  have h := (budget_root_mean_barrier_bound Finset.univ Q.width (Q.barrier W)
    (fun i _ => Q.width_nonneg i) Q.width_sum hb (fun i _ => (Q.root_spec W hb).1 i)
    (Q.root_spec W hb).2).1
  have hs : (∑ i, Q.width i * Q.barrier W i) = C / 8 * ∑ i, Q.width i ^ 3 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.barrier_constant W hC i]
    ring
  rwa [hs] at h

theorem ClosedPartition.constant_root_lower (Q : ClosedPartition n) (W : CellWeight)
    {C b : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    1 / b + C / (8 * (n : ℝ) ^ 2) ≤ Q.root W hb := by
  have hCp : 0 < C := by rw [← hC 0 ⟨le_rfl, zero_le_one⟩]; exact W.positive 0 ⟨le_rfl, zero_le_one⟩
  calc
    _ = 1 / b + C / 8 * (1 / (n : ℝ) ^ 2) := by ring
    _ ≤ 1 / b + C / 8 * ∑ i, Q.width i ^ 3 := by
      have hm : C / 8 * (1 / (n : ℝ) ^ 2) ≤ C / 8 * ∑ i, Q.width i ^ 3 :=
        mul_le_mul_of_nonneg_left Q.cubic_width_bound.1 (by positivity)
      linarith
    _ ≤ Q.root W hb := Q.constant_root_moment_bound W hC hb

theorem StrictPartition.uniform_constant_root (W : CellWeight) (hn : 0 < n)
    {C b : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    (StrictPartition.uniform n hn).closed.root W hb = 1 / b + C / (8 * (n : ℝ) ^ 2) := by
  let Q := (StrictPartition.uniform n hn).closed
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hw (i : Fin n) : Q.width i = 1 / (n : ℝ) := StrictPartition.uniform_width hn i
  have hR (i : Fin n) : Q.barrier W i = C / (8 * (n : ℝ) ^ 2) := by
    rw [Q.barrier_constant W hC i, hw i]
    field_simp
  apply (Q.eq_root W hb ?_ ?_).symm
  · intro i
    rw [hR i]
    linarith [one_div_pos.mpr hb]
  · unfold budget
    simp_rw [hw, hR]
    have he : 1 / b + C / (8 * (n : ℝ) ^ 2) - C / (8 * (n : ℝ) ^ 2) = 1 / b := by ring
    rw [he]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn0, ne_of_gt hb]

theorem ClosedPartition.constant_root_eq_iff_width (Q : ClosedPartition n) (W : CellWeight)
    {C b : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    Q.root W hb = 1 / b + C / (8 * (n : ℝ) ^ 2) ↔ ∀ i, Q.width i = 1 / (n : ℝ) := by
  constructor
  · intro he
    have hCp : 0 < C := by rw [← hC 0 ⟨le_rfl, zero_le_one⟩]; exact W.positive 0 ⟨le_rfl, zero_le_one⟩
    have hm := Q.constant_root_moment_bound W hC hb
    rw [he, show C / (8 * (n : ℝ) ^ 2) = C / 8 * (1 / (n : ℝ) ^ 2) by ring] at hm
    have hu : (∑ i, Q.width i ^ 3) ≤ 1 / (n : ℝ) ^ 2 :=
      le_of_mul_le_mul_left (show C / 8 * (∑ i, Q.width i ^ 3) ≤ C / 8 * (1 / (n : ℝ) ^ 2) by linarith)
        (by positivity)
    exact Q.cubic_width_bound.2.mp (le_antisymm hu Q.cubic_width_bound.1)
  · intro hw
    rw [Q.eq_uniform_of_width Q.size_pos hw]
    exact StrictPartition.uniform_constant_root W Q.size_pos hC hb

theorem ClosedPartition.constant_root_eq_iff_uniform (Q : ClosedPartition n) (W : CellWeight)
    (hn : 0 < n) {C b : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    Q.root W hb = 1 / b + C / (8 * (n : ℝ) ^ 2) ↔ Q = (StrictPartition.uniform n hn).closed := by
  rw [Q.constant_root_eq_iff_width W hC hb]
  constructor
  · exact Q.eq_uniform_of_width hn
  · rintro rfl i
    exact StrictPartition.uniform_width hn i

theorem StrictPartition.constant_minimizer_iff (Q : StrictPartition n) (W : CellWeight)
    (hn : 0 < n) {C b : ℝ} (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hb : 0 < b) :
    (∀ P : StrictPartition n, Q.closed.root W hb ≤ P.closed.root W hb) ↔ Q = StrictPartition.uniform n hn := by
  constructor
  · intro hmin
    have hu := hmin (StrictPartition.uniform n hn)
    rw [StrictPartition.uniform_constant_root W hn hC hb] at hu
    have he := le_antisymm hu (Q.closed.constant_root_lower W hC hb)
    exact Q.eq_uniform_of_width hn ((Q.closed.constant_root_eq_iff_width W hC hb).mp he)
  · rintro rfl P
    rw [StrictPartition.uniform_constant_root W hn hC hb]
    exact P.closed.constant_root_lower W hC hb

end TimeTraps.Interval
