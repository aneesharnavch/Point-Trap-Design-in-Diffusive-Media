module

public import TimeTraps.Probability.ReflectedFoldAffine
public import Mathlib.Data.Real.Sign
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-! Symmetric finite absolute-value sums for the triangular fold, paired
at the centres ±jL. Their formal slopes are the corresponding finite sums
of signs, with sign zero equal to zero. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Probability

noncomputable section

def reflectedFoldTanakaApprox (L : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  |z| + ∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) *
    (|z - (j + 1 : ℕ) * L| + |z + (j + 1 : ℕ) * L| - 2 * (j + 1 : ℕ) * L)

def reflectedFoldTanakaSlopeApprox (L : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  Real.sign z + ∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) *
    (Real.sign (z - (j + 1 : ℕ) * L) + Real.sign (z + (j + 1 : ℕ) * L))

theorem reflectedFoldTanakaApprox_zero (L z : ℝ) : reflectedFoldTanakaApprox L 0 z = |z| := by
  simp [reflectedFoldTanakaApprox]

theorem reflectedFoldTanakaSlopeApprox_zero (L z : ℝ) :
    reflectedFoldTanakaSlopeApprox L 0 z = Real.sign z := by
  simp [reflectedFoldTanakaSlopeApprox]

theorem reflectedFoldTanakaApprox_succ (L z : ℝ) (N : ℕ) :
    reflectedFoldTanakaApprox L (N + 1) z = reflectedFoldTanakaApprox L N z +
      (-1 : ℝ) ^ (N + 1) * (|z - (N + 1 : ℕ) * L| + |z + (N + 1 : ℕ) * L| -
        2 * (N + 1 : ℕ) * L) := by
  simp only [reflectedFoldTanakaApprox, Finset.sum_range_succ]
  ring

theorem reflectedFoldTanakaSlopeApprox_succ (L z : ℝ) (N : ℕ) :
    reflectedFoldTanakaSlopeApprox L (N + 1) z = reflectedFoldTanakaSlopeApprox L N z +
      (-1 : ℝ) ^ (N + 1) * (Real.sign (z - (N + 1 : ℕ) * L) + Real.sign (z + (N + 1 : ℕ) * L)) := by
  simp only [reflectedFoldTanakaSlopeApprox, Finset.sum_range_succ]
  ring

theorem reflectedFoldTanakaApprox_neg (L z : ℝ) (N : ℕ) :
    reflectedFoldTanakaApprox L N (-z) = reflectedFoldTanakaApprox L N z := by
  unfold reflectedFoldTanakaApprox
  rw [abs_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show -z - (j + 1 : ℕ) * L = -(z + (j + 1 : ℕ) * L) by ring,
    show -z + (j + 1 : ℕ) * L = -(z - (j + 1 : ℕ) * L) by ring, abs_neg, abs_neg]
  ring

theorem reflectedFoldTanakaSlopeApprox_neg (L z : ℝ) (N : ℕ) :
    reflectedFoldTanakaSlopeApprox L N (-z) = -reflectedFoldTanakaSlopeApprox L N z := by
  unfold reflectedFoldTanakaSlopeApprox
  rw [Real.sign_neg, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show -z - (j + 1 : ℕ) * L = -(z + (j + 1 : ℕ) * L) by ring,
    show -z + (j + 1 : ℕ) * L = -(z - (j + 1 : ℕ) * L) by ring,
    Real.sign_neg, Real.sign_neg]
  ring

theorem reflectedFoldTanakaApprox_tail (L : ℝ) (hL : 0 < L) (N : ℕ) (z : ℝ)
    (hz : (N : ℝ) * L ≤ z) :
    reflectedFoldTanakaApprox L N z =
      (1 - (-1 : ℝ) ^ N) * L / 2 + (-1 : ℝ) ^ N * (z - N * L) := by
  induction N with
  | zero =>
      simp only [Nat.cast_zero, zero_mul] at hz
      simpa only [reflectedFoldTanakaApprox_zero, pow_zero, sub_self, zero_mul, zero_div,
        Nat.cast_zero, sub_zero, one_mul, zero_add] using abs_of_nonneg hz
  | succ N ih =>
      have hn : (N : ℝ) * L ≤ z := (mul_le_mul_of_nonneg_right
        (show (N : ℝ) ≤ (N + 1 : ℕ) by exact_mod_cast Nat.le_succ N) hL.le).trans hz
      have hz0 : 0 ≤ z := (mul_nonneg (Nat.cast_nonneg N) hL.le).trans hn
      have hp : 0 ≤ z + (N + 1 : ℕ) * L := by positivity
      rw [reflectedFoldTanakaApprox_succ, ih hn, abs_of_nonneg (sub_nonneg.mpr hz), abs_of_nonneg hp]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem reflectedFoldTanakaSlopeApprox_tail (L : ℝ) (hL : 0 < L) (N : ℕ) (z : ℝ)
    (hz : (N : ℝ) * L < z) : reflectedFoldTanakaSlopeApprox L N z = (-1 : ℝ) ^ N := by
  induction N with
  | zero =>
      simp only [Nat.cast_zero, zero_mul] at hz
      simpa only [reflectedFoldTanakaSlopeApprox_zero, pow_zero, Nat.cast_zero, zero_mul] using Real.sign_of_pos hz
  | succ N ih =>
      have hn : (N : ℝ) * L < z := lt_of_le_of_lt (mul_le_mul_of_nonneg_right
        (show (N : ℝ) ≤ (N + 1 : ℕ) by exact_mod_cast Nat.le_succ N) hL.le) hz
      have hz0 : 0 < z := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg N) hL.le) hn
      have hp : 0 < z + (N + 1 : ℕ) * L := by positivity
      rw [reflectedFoldTanakaSlopeApprox_succ, ih hn, Real.sign_of_pos (sub_pos.mpr hz), Real.sign_of_pos hp]
      simp only [pow_succ]
      ring

end

end TimeTraps.Analysis
