module

public import TimeTraps.Analysis.ReflectedFoldTanakaData
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

/-! The finite sign sums have absolute value at most one, including
their corners, and stabilize at every fixed input. The stabilized function
is selected by an explicit finite cutoff; no infinite sign series is used. -/

noncomputable section

namespace TimeTraps.Analysis

open Set Filter MeasureTheory
open scoped Topology

theorem reflectedFoldTanakaSlopeApprox_step_eq (L z : ℝ) (N : ℕ)
    (hz : |z| < (N + 1 : ℕ) * L) :
    reflectedFoldTanakaSlopeApprox L (N + 1) z = reflectedFoldTanakaSlopeApprox L N z := by
  have hh := abs_lt.mp hz
  rw [reflectedFoldTanakaSlopeApprox_succ,
    Real.sign_of_neg (by linarith : z - (N + 1 : ℕ) * L < 0),
    Real.sign_of_pos (by linarith : 0 < z + (N + 1 : ℕ) * L)]
  ring

theorem reflectedFoldTanakaSlopeApprox_corner (L : ℝ) (hL : 0 < L) (N : ℕ) :
    reflectedFoldTanakaSlopeApprox L (N + 1) ((N + 1 : ℕ) * L) = 0 := by
  have hn : (N : ℝ) * L < (N + 1 : ℕ) * L :=
    mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self N) hL
  have hp : 0 < (N + 1 : ℕ) * L + (N + 1 : ℕ) * L := by positivity
  rw [reflectedFoldTanakaSlopeApprox_succ, reflectedFoldTanakaSlopeApprox_tail L hL N _ hn,
    sub_self, Real.sign_zero, Real.sign_of_pos hp]
  simp only [pow_succ]
  ring

theorem reflectedFoldTanakaSlopeApprox_bound_nonneg (L : ℝ) (hL : 0 < L)
    (N : ℕ) (z : ℝ) (hz : 0 ≤ z) : |reflectedFoldTanakaSlopeApprox L N z| ≤ 1 := by
  induction N with
  | zero =>
      rw [reflectedFoldTanakaSlopeApprox_zero]
      rcases Real.sign_apply_eq z with he | he | he <;> simp [he]
  | succ N ih =>
      rcases lt_trichotomy z ((N + 1 : ℕ) * L) with hr | hr | hr
      · rw [reflectedFoldTanakaSlopeApprox_step_eq L z N (by rwa [abs_of_nonneg hz])]
        exact ih
      · subst z
        rw [reflectedFoldTanakaSlopeApprox_corner L hL N]
        simp
      · rw [reflectedFoldTanakaSlopeApprox_tail L hL (N + 1) z hr]
        simp

theorem reflectedFoldTanakaSlopeApprox_bound (L : ℝ) (hL : 0 < L) (N : ℕ) (z : ℝ) :
    |reflectedFoldTanakaSlopeApprox L N z| ≤ 1 := by
  by_cases hz : 0 ≤ z
  · exact reflectedFoldTanakaSlopeApprox_bound_nonneg L hL N z hz
  · have hh := reflectedFoldTanakaSlopeApprox_bound_nonneg L hL N (-z) (by linarith)
    rwa [reflectedFoldTanakaSlopeApprox_neg, abs_neg] at hh

theorem reflectedFoldTanakaSlopeApprox_stable (L : ℝ) (hL : 0 < L) (z : ℝ)
    {N M : ℕ} (hNM : N ≤ M) (hz : |z| < (N + 1 : ℕ) * L) :
    reflectedFoldTanakaSlopeApprox L M z = reflectedFoldTanakaSlopeApprox L N z := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
      have hm : |z| < (M + 1 : ℕ) * L := lt_of_lt_of_le hz
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hNM 1) hL.le)
      rw [reflectedFoldTanakaSlopeApprox_step_eq L z M hm, ih]

def reflectedFoldSlope (L z : ℝ) : ℝ :=
  reflectedFoldTanakaSlopeApprox L ⌈|z| / L⌉₊ z

theorem reflectedFoldTanakaSlopeApprox_eventually_eq (L : ℝ) (hL : 0 < L) (z : ℝ) :
    ∀ᶠ N : ℕ in atTop, reflectedFoldTanakaSlopeApprox L N z = reflectedFoldSlope L z := by
  have hc : |z| ≤ (⌈|z| / L⌉₊ : ℝ) * L := (div_le_iff₀ hL).mp (Nat.le_ceil (|z| / L))
  have hsize : |z| < (⌈|z| / L⌉₊ + 1 : ℕ) * L := by
    push_cast
    nlinarith
  filter_upwards [eventually_ge_atTop ⌈|z| / L⌉₊] with N hN
  exact reflectedFoldTanakaSlopeApprox_stable L hL z hN hsize

theorem reflectedFoldTanakaSlopeApprox_tendsto (L : ℝ) (hL : 0 < L) (z : ℝ) :
    Tendsto (fun N => reflectedFoldTanakaSlopeApprox L N z) atTop (𝓝 (reflectedFoldSlope L z)) := by
  have he : (fun N => reflectedFoldTanakaSlopeApprox L N z) =ᶠ[atTop] (fun _ => reflectedFoldSlope L z) :=
    reflectedFoldTanakaSlopeApprox_eventually_eq L hL z
  exact tendsto_const_nhds.congr' he.symm

theorem reflectedFoldSlope_bound (L : ℝ) (hL : 0 < L) (z : ℝ) :
    |reflectedFoldSlope L z| ≤ 1 :=
  reflectedFoldTanakaSlopeApprox_bound L hL _ z

end TimeTraps.Analysis

end
