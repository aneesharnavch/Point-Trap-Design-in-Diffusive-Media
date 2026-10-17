module

public import TimeTraps.Analysis.ReflectedFoldTanakaRepresentation

@[expose] public section

/-! Finite symmetric absolute-value expressions for a kink of the folded
coordinate. Each new period contributes the two interior preimage pairs
with coefficient +1 and the two boundary pairs with coefficient -1. -/

noncomputable section

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Probability
open scoped Topology

def symmetricAbsPair (r z : ℝ) : ℝ := |z - r| + |z + r| - 2 * r

def reflectedInteriorTanakaApprox (L a : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  a - |z| + symmetricAbsPair a z + ∑ j ∈ Finset.range N,
    (symmetricAbsPair ((2 * (j + 1) : ℕ) * L - a) z +
      symmetricAbsPair ((2 * (j + 1) : ℕ) * L + a) z -
      symmetricAbsPair ((2 * j + 1 : ℕ) * L) z -
      symmetricAbsPair ((2 * (j + 1) : ℕ) * L) z)

theorem symmetricAbsPair_neg (r z : ℝ) : symmetricAbsPair r (-z) = symmetricAbsPair r z := by
  unfold symmetricAbsPair
  rw [show -z - r = -(z + r) by ring, show -z + r = -(z - r) by ring,
    abs_neg, abs_neg]
  ring

theorem symmetricAbsPair_zero {r z : ℝ} (hz : |z| ≤ r) : symmetricAbsPair r z = 0 := by
  have hh := abs_le.mp hz
  rw [symmetricAbsPair, abs_of_nonpos (by linarith : z - r ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ z + r)]
  ring

theorem symmetricAbsPair_tail {r z : ℝ} (hr : 0 ≤ r) (hz : r ≤ z) :
    symmetricAbsPair r z = 2 * (z - r) := by
  rw [symmetricAbsPair, abs_of_nonneg (sub_nonneg.mpr hz),
    abs_of_nonneg (by linarith : 0 ≤ z + r)]
  ring

theorem symmetricAbsPair_kink (a z : ℝ) (ha : 0 ≤ a) :
    a - |z| + symmetricAbsPair a z = |(|z| - a)| := by
  have hp (w : ℝ) (hw : 0 ≤ w) : a - |w| + symmetricAbsPair a w = |(|w| - a)| := by
    rw [abs_of_nonneg hw]
    by_cases hwa : w ≤ a
    · rw [symmetricAbsPair_zero (by rwa [abs_of_nonneg hw]),
        abs_of_nonpos (sub_nonpos.mpr hwa)]
      ring
    · rw [symmetricAbsPair_tail ha (le_of_not_ge hwa),
        abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hwa))]
      ring
  by_cases hz : 0 ≤ z
  · exact hp z hz
  · have hh := hp (-z) (by linarith)
    rwa [symmetricAbsPair_neg, abs_neg] at hh

theorem reflectedInteriorTanakaApprox_zero (L a z : ℝ) :
    reflectedInteriorTanakaApprox L a 0 z = a - |z| + symmetricAbsPair a z := by
  simp only [reflectedInteriorTanakaApprox, Finset.range_zero, Finset.sum_empty, add_zero]

theorem reflectedInteriorTanakaApprox_succ (L a z : ℝ) (N : ℕ) :
    reflectedInteriorTanakaApprox L a (N + 1) z = reflectedInteriorTanakaApprox L a N z +
      (symmetricAbsPair ((2 * (N + 1) : ℕ) * L - a) z +
        symmetricAbsPair ((2 * (N + 1) : ℕ) * L + a) z -
        symmetricAbsPair ((2 * N + 1 : ℕ) * L) z -
        symmetricAbsPair ((2 * (N + 1) : ℕ) * L) z) := by
  simp only [reflectedInteriorTanakaApprox, Finset.sum_range_succ]
  ring

theorem reflectedInteriorTanakaApprox_neg (L a z : ℝ) (N : ℕ) :
    reflectedInteriorTanakaApprox L a N (-z) = reflectedInteriorTanakaApprox L a N z := by
  simp only [reflectedInteriorTanakaApprox, symmetricAbsPair_neg, abs_neg]

theorem reflectedInteriorTanakaApprox_step_eq (L a z : ℝ) (N : ℕ)
    (hL : 0 < L) (ha : a ∈ Icc 0 L) (hz : |z| ≤ (2 * N + 1 : ℕ) * L) :
    reflectedInteriorTanakaApprox L a (N + 1) z = reflectedInteriorTanakaApprox L a N z := by
  have hp : |z| ≤ (2 * (N + 1) : ℕ) * L - a := by push_cast at hz ⊢; nlinarith [ha.2]
  have hq : |z| ≤ (2 * (N + 1) : ℕ) * L + a := by push_cast at hz ⊢; nlinarith [ha.1]
  have hc : |z| ≤ (2 * (N + 1) : ℕ) * L := by push_cast at hz ⊢; nlinarith
  rw [reflectedInteriorTanakaApprox_succ, symmetricAbsPair_zero hp, symmetricAbsPair_zero hq,
    symmetricAbsPair_zero hz, symmetricAbsPair_zero hc]
  ring

theorem reflectedInteriorTanakaApprox_tail (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Icc 0 L) (hz : (2 * N : ℕ) * L + a ≤ z) :
    reflectedInteriorTanakaApprox L a N z = z - (2 * N : ℕ) * L - a := by
  induction N with
  | zero =>
      simp only [Nat.mul_zero, Nat.cast_zero, zero_mul, zero_add] at hz
      rw [reflectedInteriorTanakaApprox_zero, abs_of_nonneg (ha.1.trans hz),
        symmetricAbsPair_tail ha.1 hz]
      simp only [Nat.mul_zero, Nat.cast_zero, zero_mul]
      ring
  | succ N ih =>
      have hprev : (2 * N : ℕ) * L + a ≤ z := by push_cast at hz ⊢; nlinarith
      have hp0 : 0 ≤ (2 * (N + 1) : ℕ) * L - a := by push_cast; nlinarith [ha.2, Nat.cast_nonneg (α := ℝ) N]
      have hq0 : 0 ≤ (2 * (N + 1) : ℕ) * L + a :=
        add_nonneg (mul_nonneg (Nat.cast_nonneg _) hL.le) ha.1
      have hb0 : 0 ≤ (2 * N + 1 : ℕ) * L := by positivity
      have hc0 : 0 ≤ (2 * (N + 1) : ℕ) * L := by positivity
      have hp : (2 * (N + 1) : ℕ) * L - a ≤ z := by nlinarith [ha.1]
      have hb : (2 * N + 1 : ℕ) * L ≤ z := by push_cast at hz ⊢; nlinarith [ha.1]
      have hc : (2 * (N + 1) : ℕ) * L ≤ z := by nlinarith [ha.1]
      rw [reflectedInteriorTanakaApprox_succ, ih hprev,
        symmetricAbsPair_tail hp0 hp, symmetricAbsPair_tail hq0 hz,
        symmetricAbsPair_tail hb0 hb, symmetricAbsPair_tail hc0 hc]
      push_cast
      ring

end TimeTraps.Analysis

end
