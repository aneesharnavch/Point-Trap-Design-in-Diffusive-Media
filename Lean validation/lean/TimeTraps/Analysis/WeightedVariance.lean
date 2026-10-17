module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace TimeTraps.Analysis

open scoped BigOperators

variable {ι : Type*}

/-- Exact weighted-square expansion, before any inequality discards a term. -/
theorem weighted_variance_identity (s : Finset ι) (w x : ι → ℝ)
    {W S : ℝ} (hW : W ≠ 0) (hw : ∑ i ∈ s, w i = W)
    (hx : ∑ i ∈ s, w i * x i = S) :
    (∑ i ∈ s, w i * (x i - S / W) ^ 2) =
      (∑ i ∈ s, w i * x i ^ 2) - S ^ 2 / W := by
  calc
    _ = ∑ i ∈ s, (w i * x i ^ 2 - (2 * (S / W)) * (w i * x i) +
        (S / W) ^ 2 * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, hx]
      field_simp
      ring

/-- Weighted Cauchy--Schwarz with the full equality condition, allowing zero weights. -/
theorem weighted_second_moment_bound (s : Finset ι) (w x : ι → ℝ)
    {W S : ℝ} (hW : 0 < W) (hw : ∑ i ∈ s, w i = W)
    (hx : ∑ i ∈ s, w i * x i = S) (hpos : ∀ i ∈ s, 0 ≤ w i) :
    S ^ 2 / W ≤ (∑ i ∈ s, w i * x i ^ 2) ∧
      ((∑ i ∈ s, w i * x i ^ 2) = S ^ 2 / W ↔
        ∀ i ∈ s, 0 < w i → x i = S / W) := by
  have hid := weighted_variance_identity s w x (ne_of_gt hW) hw hx
  have hnonneg : ∀ i ∈ s, 0 ≤ w i * (x i - S / W) ^ 2 :=
    fun i hi => mul_nonneg (hpos i hi) (sq_nonneg _)
  have hsum := Finset.sum_nonneg hnonneg
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq i hi hwi
    have hzero : (∑ i ∈ s, w i * (x i - S / W) ^ 2) = 0 := by linarith
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero i hi
    have : (x i - S / W) ^ 2 = 0 := (mul_eq_zero.mp hi0).resolve_left (ne_of_gt hwi)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
  · intro heq
    have hzero : (∑ i ∈ s, w i * (x i - S / W) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rcases eq_or_lt_of_le (hpos i hi) with hwi | hwi
      · rw [← hwi, zero_mul]
      · rw [heq i hi hwi, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
    linarith

/-- Pairwise form of the same variance; the factor 1/2 counts each unordered
pair once and does not require imposing an order on the index type. -/
theorem weighted_pairwise_identity (s : Finset ι) (w x : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (x i - x j) ^ 2) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) -
        (∑ i ∈ s, w i * x i) ^ 2) := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (w i * x i ^ 2 * w j + w i * (w j * x j ^ 2) -
          2 * (w i * x i) * (w j * x j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]
      ring

end TimeTraps.Analysis
