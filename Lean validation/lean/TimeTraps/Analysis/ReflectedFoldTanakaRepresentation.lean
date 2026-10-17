module

public import TimeTraps.Analysis.ReflectedFoldTanakaData

@[expose] public section

/-! Exact equality of the finite symmetric absolute-value expression
with the triangular fold on each expanding interval. The proof uses
the fold's actual affine cells and the explicit tails of the finite sum. -/

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Probability
open scoped Topology

theorem reflectedFold_nat_cell (L : ℝ) (hL : 0 < L) (N : ℕ) (r : ℝ)
    (hr : r ∈ Icc 0 L) : reflectedFold L (r + N * L) =
      (1 - (-1 : ℝ) ^ N) * L / 2 + (-1 : ℝ) ^ N * r := by
  rcases Nat.even_or_odd N with hn | hn
  · have hp : (-1 : ℝ) ^ N = 1 := hn.neg_one_pow
    rcases hn with ⟨k, rfl⟩
    rw [show r + (k + k : ℕ) * L = r + (k : ℤ) * (2 * L) by push_cast; ring,
      reflectedFold_int_period, reflectedFold_eq_self L hL r hr, hp]
    ring
  · have hp : (-1 : ℝ) ^ N = -1 := hn.neg_one_pow
    rcases hn with ⟨k, rfl⟩
    rw [show r + (2 * k + 1 : ℕ) * L = (r + L) + (k : ℤ) * (2 * L) by push_cast; ring,
      reflectedFold_int_period, hp]
    have hf := reflectedFold_falling L hL 1 (r + L)
      (show r + L ∈ Icc ((1 : ℤ) * (2 * L) - L) ((1 : ℤ) * (2 * L)) by
        norm_num
        constructor <;> linarith [hr.1, hr.2])
    norm_num at hf
    linarith

theorem reflectedFoldTanakaApprox_step_eq (L z : ℝ) (N : ℕ)
    (hz : |z| ≤ (N + 1 : ℕ) * L) :
    reflectedFoldTanakaApprox L (N + 1) z = reflectedFoldTanakaApprox L N z := by
  have hh := abs_le.mp hz
  rw [reflectedFoldTanakaApprox_succ,
    abs_of_nonpos (by linarith : z - (N + 1 : ℕ) * L ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ z + (N + 1 : ℕ) * L)]
  ring

theorem reflectedFoldTanakaApprox_eq_nonneg (L : ℝ) (hL : 0 < L) (N : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hN : z ≤ (N + 1 : ℕ) * L) :
    reflectedFoldTanakaApprox L N z = reflectedFold L z := by
  induction N with
  | zero =>
      simp only [Nat.zero_add, Nat.cast_one, one_mul] at hN
      rw [reflectedFoldTanakaApprox_zero, abs_of_nonneg hz, reflectedFold_eq_self L hL z ⟨hz, hN⟩]
  | succ N ih =>
      by_cases hi : z ≤ (N + 1 : ℕ) * L
      · rw [reflectedFoldTanakaApprox_step_eq L z N (by rwa [abs_of_nonneg hz])]
        exact ih hi
      · have hlo : (N + 1 : ℕ) * L ≤ z := (lt_of_not_ge hi).le
        rw [reflectedFoldTanakaApprox_tail L hL (N + 1) z hlo]
        have hr : z - (N + 1 : ℕ) * L ∈ Icc 0 L := by
          constructor
          · linarith
          · push_cast at hN ⊢
            nlinarith
        have hf := reflectedFold_nat_cell L hL (N + 1) (z - (N + 1 : ℕ) * L) hr
        rw [sub_add_cancel] at hf
        exact hf.symm

theorem reflectedFoldTanakaApprox_eq (L : ℝ) (hL : 0 < L) (N : ℕ) (z : ℝ)
    (hz : |z| ≤ (N + 1 : ℕ) * L) :
    reflectedFoldTanakaApprox L N z = reflectedFold L z := by
  by_cases hp : 0 ≤ z
  · exact reflectedFoldTanakaApprox_eq_nonneg L hL N z hp (by rwa [abs_of_nonneg hp] at hz)
  · have hh := reflectedFoldTanakaApprox_eq_nonneg L hL N (-z) (by linarith)
      (by rwa [abs_of_neg (lt_of_not_ge hp)] at hz)
    rwa [reflectedFoldTanakaApprox_neg, reflectedFold_neg] at hh

theorem reflectedFoldTanakaApprox_eventually_eq (L : ℝ) (hL : 0 < L) (z : ℝ) :
    ∀ᶠ N : ℕ in atTop, reflectedFoldTanakaApprox L N z = reflectedFold L z := by
  have hc : |z| ≤ (⌈|z| / L⌉₊ : ℝ) * L := (div_le_iff₀ hL).mp (Nat.le_ceil (|z| / L))
  filter_upwards [eventually_ge_atTop ⌈|z| / L⌉₊] with N hN
  apply reflectedFoldTanakaApprox_eq L hL N z
  exact hc.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast le_trans hN (Nat.le_succ N)) hL.le)

end TimeTraps.Analysis
