module

public import TimeTraps.Analysis.ReflectedInteriorTanakaData
public import TimeTraps.Analysis.ReflectedFoldTanakaGeometry

@[expose] public section

/-! The midpoint slopes of the finite interior-kink expressions.
The positive and negative preimages use the same actual sign convention. -/

noncomputable section

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Probability
open scoped Topology

def symmetricSignPair (r z : ℝ) : ℝ := Real.sign (z - r) + Real.sign (z + r)

def reflectedInteriorTanakaSlopeApprox (L a : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  -Real.sign z + symmetricSignPair a z + ∑ j ∈ Finset.range N,
    (symmetricSignPair ((2 * (j + 1) : ℕ) * L - a) z +
      symmetricSignPair ((2 * (j + 1) : ℕ) * L + a) z -
      symmetricSignPair ((2 * j + 1 : ℕ) * L) z -
      symmetricSignPair ((2 * (j + 1) : ℕ) * L) z)

def reflectedInteriorTanakaSlope (L a z : ℝ) : ℝ :=
  Real.sign (reflectedFold L z - a) * reflectedFoldSlope L z

theorem symmetricSignPair_neg (r z : ℝ) : symmetricSignPair r (-z) = -symmetricSignPair r z := by
  unfold symmetricSignPair
  rw [show -z - r = -(z + r) by ring, show -z + r = -(z - r) by ring,
    Real.sign_neg, Real.sign_neg]
  ring

theorem symmetricSignPair_zero {r z : ℝ} (hz : |z| < r) : symmetricSignPair r z = 0 := by
  have hh := abs_lt.mp hz
  rw [symmetricSignPair, Real.sign_of_neg (by linarith : z - r < 0),
    Real.sign_of_pos (by linarith : 0 < z + r)]
  ring

theorem symmetricSignPair_tail {r z : ℝ} (hr : 0 ≤ r) (hz : r < z) :
    symmetricSignPair r z = 2 := by
  rw [symmetricSignPair, Real.sign_of_pos (sub_pos.mpr hz),
    Real.sign_of_pos (by linarith : 0 < z + r)]
  ring

theorem symmetricSignPair_corner {r : ℝ} (hr : 0 < r) : symmetricSignPair r r = 1 := by
  rw [symmetricSignPair, sub_self, Real.sign_zero, Real.sign_of_pos (by linarith : 0 < r + r), zero_add]

theorem symmetricSignPair_kink (a z : ℝ) (ha : 0 < a) :
    -Real.sign z + symmetricSignPair a z = Real.sign (|z| - a) * Real.sign z := by
  have hp (w : ℝ) (hw : 0 ≤ w) :
      -Real.sign w + symmetricSignPair a w = Real.sign (|w| - a) * Real.sign w := by
    by_cases hw0 : w = 0
    · subst w
      simp only [symmetricSignPair, zero_sub, zero_add, Real.sign_neg, Real.sign_zero,
        neg_zero, abs_zero, mul_zero]
      ring
    · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
      rw [Real.sign_of_pos hwpos, abs_of_nonneg hw, mul_one]
      rcases lt_trichotomy w a with hwa | hwa | hwa
      · rw [symmetricSignPair_zero (by rwa [abs_of_nonneg hw]), Real.sign_of_neg (sub_neg.mpr hwa)]
        ring
      · subst w
        rw [symmetricSignPair_corner ha, sub_self, Real.sign_zero]
        ring
      · rw [symmetricSignPair_tail ha.le hwa, Real.sign_of_pos (sub_pos.mpr hwa)]
        ring
  by_cases hz : 0 ≤ z
  · exact hp z hz
  · have hh := hp (-z) (by linarith)
    rw [Real.sign_neg, symmetricSignPair_neg, abs_neg] at hh
    linear_combination -hh

theorem reflectedInteriorTanakaSlopeApprox_zero (L a z : ℝ) :
    reflectedInteriorTanakaSlopeApprox L a 0 z = -Real.sign z + symmetricSignPair a z := by
  simp only [reflectedInteriorTanakaSlopeApprox, Finset.range_zero, Finset.sum_empty, add_zero]

theorem reflectedInteriorTanakaSlopeApprox_succ (L a z : ℝ) (N : ℕ) :
    reflectedInteriorTanakaSlopeApprox L a (N + 1) z = reflectedInteriorTanakaSlopeApprox L a N z +
      (symmetricSignPair ((2 * (N + 1) : ℕ) * L - a) z +
        symmetricSignPair ((2 * (N + 1) : ℕ) * L + a) z -
        symmetricSignPair ((2 * N + 1 : ℕ) * L) z -
        symmetricSignPair ((2 * (N + 1) : ℕ) * L) z) := by
  simp only [reflectedInteriorTanakaSlopeApprox, Finset.sum_range_succ]
  ring

theorem reflectedInteriorTanakaSlopeApprox_neg (L a z : ℝ) (N : ℕ) :
    reflectedInteriorTanakaSlopeApprox L a N (-z) = -reflectedInteriorTanakaSlopeApprox L a N z := by
  simp only [reflectedInteriorTanakaSlopeApprox, symmetricSignPair_neg, Real.sign_neg]
  rw [neg_add, neg_add]
  simp only [neg_neg]
  rw [← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem reflectedInteriorTanakaSlopeApprox_step_eq (L a z : ℝ) (N : ℕ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) (hz : |z| < (2 * N + 1 : ℕ) * L) :
    reflectedInteriorTanakaSlopeApprox L a (N + 1) z = reflectedInteriorTanakaSlopeApprox L a N z := by
  have hp : |z| < (2 * (N + 1) : ℕ) * L - a := by push_cast at hz ⊢; nlinarith [ha.2]
  have hq : |z| < (2 * (N + 1) : ℕ) * L + a := by push_cast at hz ⊢; nlinarith [ha.1]
  have hc : |z| < (2 * (N + 1) : ℕ) * L := by push_cast at hz ⊢; nlinarith
  rw [reflectedInteriorTanakaSlopeApprox_succ, symmetricSignPair_zero hp, symmetricSignPair_zero hq,
    symmetricSignPair_zero hz, symmetricSignPair_zero hc]
  ring

theorem reflectedInteriorTanakaSlopeApprox_tail (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) (hz : (2 * N : ℕ) * L + a < z) :
    reflectedInteriorTanakaSlopeApprox L a N z = 1 := by
  induction N with
  | zero =>
      simp only [Nat.mul_zero, Nat.cast_zero, zero_mul, zero_add] at hz
      rw [reflectedInteriorTanakaSlopeApprox_zero, Real.sign_of_pos (ha.1.trans hz),
        symmetricSignPair_tail ha.1.le hz]
      ring
  | succ N ih =>
      have hprev : (2 * N : ℕ) * L + a < z := by push_cast at hz ⊢; nlinarith
      have hp0 : 0 ≤ (2 * (N + 1) : ℕ) * L - a := by push_cast; nlinarith [ha.2, Nat.cast_nonneg (α := ℝ) N]
      have hq0 : 0 ≤ (2 * (N + 1) : ℕ) * L + a :=
        add_nonneg (mul_nonneg (Nat.cast_nonneg _) hL.le) ha.1.le
      have hb0 : 0 ≤ (2 * N + 1 : ℕ) * L := by positivity
      have hc0 : 0 ≤ (2 * (N + 1) : ℕ) * L := by positivity
      have hp : (2 * (N + 1) : ℕ) * L - a < z := by nlinarith [ha.1]
      have hb : (2 * N + 1 : ℕ) * L < z := by push_cast at hz ⊢; nlinarith [ha.1]
      have hc : (2 * (N + 1) : ℕ) * L < z := by nlinarith [ha.1]
      rw [reflectedInteriorTanakaSlopeApprox_succ, ih hprev,
        symmetricSignPair_tail hp0 hp, symmetricSignPair_tail hq0 hz,
        symmetricSignPair_tail hb0 hb, symmetricSignPair_tail hc0 hc]
      ring

end TimeTraps.Analysis

end
