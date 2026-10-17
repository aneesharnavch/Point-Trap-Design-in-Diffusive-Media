module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPathClockData

@[expose] public section

/-! Sampling by a positive clock depends only on the reference path
before its inverse time. The integral and inverse equalities below remove
the auxiliary constant continuation of the finite-horizon path. -/

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis
open scoped NNReal

theorem reflectedMarkovPathSpeed_clock_agrees
    (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y)
    (p : ReflectedMarkovPath L H) (v : PositiveTimeSpeed) (Y : ℝ≥0 → Icc (0 : ℝ) L)
    (hrate : ∀ s, v.rate s = c (Y s))
    (hp : ∀ s : Icc (0 : ℝ≥0) H, p s = Y s.val)
    {s : ℝ≥0} (hs : s ≤ H) :
    (reflectedMarkovPathSpeed L hL H c hc hpos p).clock s = v.clock s := by
  apply NNReal.eq
  rw [PositiveTimeSpeed.clock_coe, PositiveTimeSpeed.clock_coe]
  apply intervalIntegral.integral_congr_Ioo_of_le s.coe_nonneg
  intro r hr
  have hrH : r.toNNReal ≤ H :=
    Real.toNNReal_le_iff_le_coe.mpr (hr.2.le.trans (show s.val ≤ H.val from hs))
  change (reflectedMarkovPathSpeed L hL H c hc hpos p).rate r.toNNReal = v.rate r.toNNReal
  rw [reflectedMarkovPathSpeed_rate, hrate]
  apply congrArg c
  change p ⟨min r.toNNReal H, bot_le, min_le_right _ _⟩ = Y r.toNNReal
  simpa only [min_eq_left hrH] using hp ⟨r.toNNReal, bot_le, hrH⟩

theorem reflectedMarkovPathSpeed_inverse_agrees
    (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y)
    (p : ReflectedMarkovPath L H) (v : PositiveTimeSpeed) (Y : ℝ≥0 → Icc (0 : ℝ) L)
    (hrate : ∀ s, v.rate s = c (Y s))
    (hp : ∀ s : Icc (0 : ℝ≥0) H, p s = Y s.val)
    {t : ℝ≥0} (ht : v.inverse t ≤ H) :
    (reflectedMarkovPathSpeed L hL H c hc hpos p).inverse t = v.inverse t := by
  apply (reflectedMarkovPathSpeed L hL H c hc hpos p).clock_strictMono.injective
  rw [PositiveTimeSpeed.clock_inverse,
    reflectedMarkovPathSpeed_clock_agrees L hL H c hc hpos p v Y hrate hp ht,
    v.clock_inverse]

theorem reflectedMarkovPathTimeChange_agrees
    (L : ℝ) (hL : 0 < L) (H : ℝ≥0)
    (c : Icc (0 : ℝ) L → ℝ) (hc : Continuous c) (hpos : ∀ y, 0 < c y)
    (p : ReflectedMarkovPath L H) (v : PositiveTimeSpeed) (Y : ℝ≥0 → Icc (0 : ℝ) L)
    (hrate : ∀ s, v.rate s = c (Y s))
    (hp : ∀ s : Icc (0 : ℝ≥0) H, p s = Y s.val)
    {t : ℝ≥0} (ht : v.inverse t ≤ H) :
    reflectedMarkovPathTimeChange L hL H c hc hpos t p = Y (v.inverse t) := by
  unfold reflectedMarkovPathTimeChange
  rw [reflectedMarkovPathSpeed_inverse_agrees L hL H c hc hpos p v Y hrate hp ht]
  change p ⟨min (v.inverse t) H, bot_le, min_le_right _ _⟩ = Y (v.inverse t)
  simpa only [min_eq_left ht] using hp ⟨v.inverse t, bot_le, ht⟩

end TimeTraps.Probability
