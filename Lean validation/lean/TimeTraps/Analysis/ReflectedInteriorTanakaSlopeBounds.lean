module

public import TimeTraps.Analysis.ReflectedInteriorTanakaSlopeData

@[expose] public section

/-! The finite midpoint slopes stay in [-1,1], including every finite
corner. This uniform bound is proved before using any stochastic limit. -/

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Probability
open scoped Topology

theorem symmetricSignPair_period_window (L a c z : ℝ) (ha : 0 < a)
    (hb : 0 ≤ c - L) (hp : 0 ≤ c - a) (hz : c - L < z) :
    1 + (symmetricSignPair (c - a) z + symmetricSignPair (c + a) z -
      symmetricSignPair (c - L) z - symmetricSignPair c z) =
      Real.sign (|z - c| - a) * Real.sign (z - c) := by
  have hc : 0 ≤ c := by linarith
  have hz0 : 0 < z := lt_of_le_of_lt hb hz
  have hzp : 0 < z + (c - a) := by linarith
  have hzq : 0 < z + (c + a) := by linarith
  have hzc : 0 < z + c := by linarith
  rw [symmetricSignPair_tail hb hz]
  calc
    _ = -Real.sign (z - c) + symmetricSignPair a (z - c) := by
      unfold symmetricSignPair
      rw [Real.sign_of_pos hzp, Real.sign_of_pos hzq, Real.sign_of_pos hzc,
        show z - (c - a) = z - c + a by ring,
        show z - (c + a) = z - c - a by ring]
      ring
    _ = _ := symmetricSignPair_kink a (z - c) ha

theorem reflectedInteriorTanakaSlopeApprox_outer (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) (hz : (2 * N + 1 : ℕ) * L < z) :
    reflectedInteriorTanakaSlopeApprox L a (N + 1) z =
      Real.sign (|z - (2 * (N + 1) : ℕ) * L| - a) *
        Real.sign (z - (2 * (N + 1) : ℕ) * L) := by
  have htail : (2 * N : ℕ) * L + a < z := by push_cast at hz ⊢; nlinarith [ha.2]
  have hb : 0 ≤ (2 * (N + 1) : ℕ) * L - L := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hp : 0 ≤ (2 * (N + 1) : ℕ) * L - a := by
    push_cast
    nlinarith [ha.2, Nat.cast_nonneg (α := ℝ) N]
  have hz' : (2 * (N + 1) : ℕ) * L - L < z := by push_cast at hz ⊢; nlinarith
  have he : (2 * N + 1 : ℕ) * L = (2 * (N + 1) : ℕ) * L - L := by push_cast; ring
  rw [reflectedInteriorTanakaSlopeApprox_succ,
    reflectedInteriorTanakaSlopeApprox_tail L a N z hL ha htail, he]
  exact symmetricSignPair_period_window L a _ z ha.1 hb hp hz'

theorem reflectedInteriorTanakaSlopeApprox_corner (L a : ℝ) (N : ℕ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) :
    reflectedInteriorTanakaSlopeApprox L a (N + 1) ((2 * N + 1 : ℕ) * L) = 0 := by
  have hb : 0 < (2 * N + 1 : ℕ) * L := by positivity
  have htail : (2 * N : ℕ) * L + a < (2 * N + 1 : ℕ) * L := by push_cast; nlinarith [ha.2]
  have hp : |(2 * N + 1 : ℕ) * L| < (2 * (N + 1) : ℕ) * L - a := by
    rw [abs_of_pos hb]
    push_cast
    nlinarith [ha.2]
  have hq : |(2 * N + 1 : ℕ) * L| < (2 * (N + 1) : ℕ) * L + a := by
    rw [abs_of_pos hb]
    push_cast
    nlinarith [ha.1]
  have hc : |(2 * N + 1 : ℕ) * L| < (2 * (N + 1) : ℕ) * L := by
    rw [abs_of_pos hb]
    push_cast
    nlinarith
  rw [reflectedInteriorTanakaSlopeApprox_succ,
    reflectedInteriorTanakaSlopeApprox_tail L a N _ hL ha htail,
    symmetricSignPair_zero hp, symmetricSignPair_zero hq,
    symmetricSignPair_corner hb, symmetricSignPair_zero hc]
  ring

theorem reflectedInteriorTanakaSlopeApprox_bound (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) :
    |reflectedInteriorTanakaSlopeApprox L a N z| ≤ 1 := by
  have hs (u v : ℝ) : |Real.sign u * Real.sign v| ≤ 1 := by
    rcases Real.sign_apply_eq u with hu | hu | hu <;>
      rcases Real.sign_apply_eq v with hv | hv | hv <;> rw [hu, hv] <;> norm_num
  have hp (n : ℕ) (w : ℝ) (hw : 0 ≤ w) :
      |reflectedInteriorTanakaSlopeApprox L a n w| ≤ 1 := by
    induction n with
    | zero =>
        rw [reflectedInteriorTanakaSlopeApprox_zero, symmetricSignPair_kink a w ha.1]
        exact hs _ _
    | succ n ih =>
        rcases lt_trichotomy w ((2 * n + 1 : ℕ) * L) with hn | hn | hn
        · rw [reflectedInteriorTanakaSlopeApprox_step_eq L a w n hL ha
            (by rwa [abs_of_nonneg hw])]
          exact ih
        · subst w
          rw [reflectedInteriorTanakaSlopeApprox_corner L a n hL ha]
          norm_num
        · rw [reflectedInteriorTanakaSlopeApprox_outer L a n w hL ha hn]
          exact hs _ _
  by_cases hz : 0 ≤ z
  · exact hp N z hz
  · have hh := hp N (-z) (by linarith)
    rwa [reflectedInteriorTanakaSlopeApprox_neg, abs_neg] at hh

theorem reflectedInteriorTanakaSlopeApprox_stable (L a z : ℝ) (hL : 0 < L)
    (ha : a ∈ Ioo 0 L) {N M : ℕ} (hNM : N ≤ M) (hz : |z| < (2 * N + 1 : ℕ) * L) :
    reflectedInteriorTanakaSlopeApprox L a M z = reflectedInteriorTanakaSlopeApprox L a N z := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
      have hm : |z| < (2 * M + 1 : ℕ) * L := lt_of_lt_of_le hz
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2 * N + 1 ≤ 2 * M + 1 by omega)) hL.le)
      rw [reflectedInteriorTanakaSlopeApprox_step_eq L a z M hL ha hm, ih]

end TimeTraps.Analysis
