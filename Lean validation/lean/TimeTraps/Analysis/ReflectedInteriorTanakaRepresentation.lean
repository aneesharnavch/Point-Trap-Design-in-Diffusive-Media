module

public import TimeTraps.Analysis.ReflectedInteriorTanakaData

@[expose] public section

/-! The finite absolute-value expression agrees with the actual kink
of the triangular fold on expanding compact intervals. -/

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Probability
open scoped Topology

theorem symmetricAbsPair_period_window (L a c z : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ c - L) (hp : 0 ≤ c - a) (hz : c - L ≤ z) :
    z - c + 2 * L - a + (symmetricAbsPair (c - a) z + symmetricAbsPair (c + a) z -
      symmetricAbsPair (c - L) z - symmetricAbsPair c z) = |(|z - c| - a)| := by
  have hc : 0 ≤ c := by linarith
  have hz0 : 0 ≤ z := hb.trans hz
  have hzp : 0 ≤ z + (c - a) := add_nonneg hz0 hp
  have hzq : 0 ≤ z + (c + a) := by linarith
  have hzc : 0 ≤ z + c := add_nonneg hz0 hc
  rw [symmetricAbsPair_tail hb hz]
  calc
    _ = a - |z - c| + symmetricAbsPair a (z - c) := by
      unfold symmetricAbsPair
      rw [abs_of_nonneg hzp, abs_of_nonneg hzq, abs_of_nonneg hzc,
        show z - (c - a) = z - c + a by ring,
        show z - (c + a) = z - c - a by ring]
      ring
    _ = _ := symmetricAbsPair_kink a (z - c) ha

theorem reflectedInteriorTanakaApprox_outer (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Icc 0 L) (hz : (2 * N + 1 : ℕ) * L ≤ z) :
    reflectedInteriorTanakaApprox L a (N + 1) z =
      |(|z - (2 * (N + 1) : ℕ) * L| - a)| := by
  have htail : (2 * N : ℕ) * L + a ≤ z := by push_cast at hz ⊢; nlinarith [ha.2]
  have hb : 0 ≤ (2 * (N + 1) : ℕ) * L - L := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hp : 0 ≤ (2 * (N + 1) : ℕ) * L - a := by
    push_cast
    nlinarith [ha.2, Nat.cast_nonneg (α := ℝ) N]
  have hz' : (2 * (N + 1) : ℕ) * L - L ≤ z := by push_cast at hz ⊢; nlinarith
  have he : (2 * N + 1 : ℕ) * L = (2 * (N + 1) : ℕ) * L - L := by push_cast; ring
  rw [reflectedInteriorTanakaApprox_succ, reflectedInteriorTanakaApprox_tail L a N z hL ha htail, he]
  have hi := symmetricAbsPair_period_window L a ((2 * (N + 1) : ℕ) * L) z ha.1 hb hp hz'
  convert hi using 1
  push_cast
  ring

theorem reflectedInteriorTanakaApprox_eq_nonneg (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Icc 0 L) (hz : 0 ≤ z)
    (hN : z ≤ (2 * N + 1 : ℕ) * L) :
    reflectedInteriorTanakaApprox L a N z = |reflectedFold L z - a| := by
  induction N with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_one, one_mul] at hN
      rw [reflectedInteriorTanakaApprox_zero, symmetricAbsPair_kink a z ha.1,
        abs_of_nonneg hz, reflectedFold_eq_self L hL z ⟨hz, hN⟩]
  | succ N ih =>
      by_cases hi : z ≤ (2 * N + 1 : ℕ) * L
      · rw [reflectedInteriorTanakaApprox_step_eq L a z N hL ha (by rwa [abs_of_nonneg hz])]
        exact ih hi
      · have hlo : (2 * N + 1 : ℕ) * L ≤ z := (lt_of_not_ge hi).le
        rw [reflectedInteriorTanakaApprox_outer L a N z hL ha hlo]
        have hb : |z - (2 * (N + 1) : ℕ) * L| ≤ L := by
          apply abs_le.mpr
          push_cast at hlo hN ⊢
          constructor <;> nlinarith
        have hf := reflectedFoldTanakaApprox_eq L hL 0 (z - (2 * (N + 1) : ℕ) * L)
          (by simpa only [Nat.zero_add, Nat.cast_one, one_mul] using hb)
        rw [reflectedFoldTanakaApprox_zero] at hf
        have he : z - (2 * (N + 1) : ℕ) * L + (N + 1 : ℤ) * (2 * L) = z := by
          push_cast
          ring
        have hp := reflectedFold_int_period L (z - (2 * (N + 1) : ℕ) * L) (N + 1 : ℤ)
        rw [he] at hp
        rw [hp, ← hf]

theorem reflectedInteriorTanakaApprox_eq (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Icc 0 L) (hz : |z| ≤ (2 * N + 1 : ℕ) * L) :
    reflectedInteriorTanakaApprox L a N z = |reflectedFold L z - a| := by
  by_cases hp : 0 ≤ z
  · exact reflectedInteriorTanakaApprox_eq_nonneg L a N z hL ha hp
      (by rwa [abs_of_nonneg hp] at hz)
  · have hh := reflectedInteriorTanakaApprox_eq_nonneg L a N (-z) hL ha (by linarith)
      (by rwa [abs_of_neg (lt_of_not_ge hp)] at hz)
    rwa [reflectedInteriorTanakaApprox_neg, reflectedFold_neg] at hh

theorem reflectedInteriorTanakaApprox_eventually_eq (L a z : ℝ)
    (hL : 0 < L) (ha : a ∈ Icc 0 L) :
    ∀ᶠ N : ℕ in atTop, reflectedInteriorTanakaApprox L a N z = |reflectedFold L z - a| := by
  have hc : |z| ≤ (⌈|z| / L⌉₊ : ℝ) * L := (div_le_iff₀ hL).mp (Nat.le_ceil (|z| / L))
  filter_upwards [eventually_ge_atTop ⌈|z| / L⌉₊] with N hN
  apply reflectedInteriorTanakaApprox_eq L a N z hL ha
  exact hc.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (show ⌈|z| / L⌉₊ ≤ 2 * N + 1 by omega)) hL.le)

end TimeTraps.Analysis
