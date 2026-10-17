module

public import TimeTraps.Analysis.ReflectedInteriorTanakaSlopeBounds

@[expose] public section

/-! Identification of the stabilized midpoint slopes with the actual
folded sign coefficient, including all fold and interior-kink corners. -/

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Probability
open scoped Topology

theorem reflectedFoldSlope_central (L z : ℝ) (hL : 0 < L) (hz : |z| < L) :
    reflectedFoldSlope L z = Real.sign z := by
  have hp (w : ℝ) (hw : |w| < L) (hw0 : 0 ≤ w) : reflectedFoldSlope L w = Real.sign w := by
    by_cases he : w = 0
    · subst w
      have h := reflectedFoldSlope_nat_corner L hL 0
      simpa only [Nat.cast_zero, zero_mul, Real.sign_zero] using h
    · have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm he)
      have hi : w ∈ Ioo 0 L := ⟨hwpos, by rwa [abs_of_nonneg hw0] at hw⟩
      have h := reflectedFoldSlope_rising L hL 0 w hi
      simpa only [Int.cast_zero, zero_mul, add_zero, Real.sign_of_pos hwpos] using h
  by_cases hz0 : 0 ≤ z
  · exact hp z hz hz0
  · have h := hp (-z) (by rwa [abs_neg]) (by linarith)
    rw [reflectedFoldSlope_neg, Real.sign_neg] at h
    exact neg_injective h

theorem reflectedInteriorTanakaSlope_neg (L a z : ℝ) :
    reflectedInteriorTanakaSlope L a (-z) = -reflectedInteriorTanakaSlope L a z := by
  rw [reflectedInteriorTanakaSlope, reflectedInteriorTanakaSlope,
    reflectedFold_neg, reflectedFoldSlope_neg, mul_neg]

theorem reflectedInteriorTanakaSlopeApprox_eq_nonneg (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) (hz : 0 ≤ z)
    (hN : z < (2 * N + 1 : ℕ) * L) :
    reflectedInteriorTanakaSlopeApprox L a N z = reflectedInteriorTanakaSlope L a z := by
  induction N with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_one, one_mul] at hN
      rw [reflectedInteriorTanakaSlopeApprox_zero, symmetricSignPair_kink a z ha.1,
        reflectedInteriorTanakaSlope, reflectedFold_eq_self L hL z ⟨hz, hN.le⟩,
        reflectedFoldSlope_central L z hL (by rwa [abs_of_nonneg hz]), abs_of_nonneg hz]
  | succ N ih =>
      rcases lt_trichotomy z ((2 * N + 1 : ℕ) * L) with hi | hi | hi
      · rw [reflectedInteriorTanakaSlopeApprox_step_eq L a z N hL ha (by rwa [abs_of_nonneg hz])]
        exact ih hi
      · subst z
        rw [reflectedInteriorTanakaSlopeApprox_corner L a N hL ha, reflectedInteriorTanakaSlope]
        have hc : reflectedFoldSlope L ((2 * N + 1 : ℕ) * L) = 0 := by
          simpa only [Int.cast_natCast] using
            reflectedFoldSlope_int_corner L hL ((2 * N + 1 : ℕ) : ℤ)
        rw [hc, mul_zero]
      · rw [reflectedInteriorTanakaSlopeApprox_outer L a N z hL ha hi]
        have hb : |z - (2 * (N + 1) : ℕ) * L| < L := by
          apply abs_lt.mpr
          push_cast at hi hN ⊢
          constructor <;> nlinarith
        have hf := reflectedFoldTanakaApprox_eq L hL 0 (z - (2 * (N + 1) : ℕ) * L)
          (by simpa only [Nat.zero_add, Nat.cast_one, one_mul] using hb.le)
        rw [reflectedFoldTanakaApprox_zero] at hf
        have he : z - (2 * (N + 1) : ℕ) * L + (N + 1 : ℤ) * (2 * L) = z := by
          push_cast
          ring
        have hp := reflectedFold_int_period L (z - (2 * (N + 1) : ℕ) * L) (N + 1 : ℤ)
        rw [he] at hp
        have hs := (reflectedFoldSlope_periodic L hL).int_mul (N + 1 : ℤ)
          (z - (2 * (N + 1) : ℕ) * L)
        rw [he] at hs
        rw [reflectedInteriorTanakaSlope, hp, ← hf, hs,
          reflectedFoldSlope_central L _ hL hb]

theorem reflectedInteriorTanakaSlopeApprox_eq (L a : ℝ) (N : ℕ) (z : ℝ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) (hz : |z| < (2 * N + 1 : ℕ) * L) :
    reflectedInteriorTanakaSlopeApprox L a N z = reflectedInteriorTanakaSlope L a z := by
  by_cases hp : 0 ≤ z
  · exact reflectedInteriorTanakaSlopeApprox_eq_nonneg L a N z hL ha hp
      (by rwa [abs_of_nonneg hp] at hz)
  · have hh := reflectedInteriorTanakaSlopeApprox_eq_nonneg L a N (-z) hL ha (by linarith)
      (by rwa [abs_of_neg (lt_of_not_ge hp)] at hz)
    rw [reflectedInteriorTanakaSlopeApprox_neg, reflectedInteriorTanakaSlope_neg] at hh
    exact neg_injective hh

theorem reflectedInteriorTanakaSlopeApprox_eventually_eq (L a z : ℝ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) :
    ∀ᶠ N : ℕ in atTop, reflectedInteriorTanakaSlopeApprox L a N z = reflectedInteriorTanakaSlope L a z := by
  have hc : |z| ≤ (⌈|z| / L⌉₊ : ℝ) * L := (div_le_iff₀ hL).mp (Nat.le_ceil (|z| / L))
  filter_upwards [eventually_ge_atTop ⌈|z| / L⌉₊] with N hN
  apply reflectedInteriorTanakaSlopeApprox_eq L a N z hL ha
  have hn : (⌈|z| / L⌉₊ : ℝ) ≤ N := by exact_mod_cast hN
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hn hL.le, Nat.cast_nonneg (α := ℝ) N]

theorem reflectedInteriorTanakaSlopeApprox_tendsto (L a z : ℝ)
    (hL : 0 < L) (ha : a ∈ Ioo 0 L) :
    Tendsto (fun N => reflectedInteriorTanakaSlopeApprox L a N z) atTop
      (𝓝 (reflectedInteriorTanakaSlope L a z)) := by
  have he : (fun N => reflectedInteriorTanakaSlopeApprox L a N z) =ᶠ[atTop]
      (fun _ => reflectedInteriorTanakaSlope L a z) :=
    reflectedInteriorTanakaSlopeApprox_eventually_eq L a z hL ha
  exact tendsto_const_nhds.congr' he.symm

end TimeTraps.Analysis
