module

public import TimeTraps.Probability.ReflectedFellerSeriesData

@[expose] public section

/-! The absolutely convergent continuous-function heat series equals
the actual reflected Feller evolution. The identification uses exact
cosine moments and their proved separation of continuous functions. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis

theorem reflectedFellerHeatTerm_pairing (L : ℝ) (hL : 0 < L) (D : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (n m : ℕ) (t : ℝ) :
    reflectedFellerPairing L hL (neumannCosine L m) (reflectedFellerHeatTerm L hL D f n t) =
      if m = n + 1 then Real.exp (-reflectedFellerHeatRate L D * (m : ℝ) ^ 2 * t) *
        reflectedFellerPairing L hL (neumannCosine L m) f else 0 := by
  rw [reflectedFellerHeatTerm, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp,
    map_smul, smul_eq_mul, reflectedFellerPairing_cosine_cosine L hL m (n + 1)]
  by_cases hm : m = n + 1
  · subst m
    simp only [if_true, Nat.add_one_ne_zero, if_false]
    ring
  · simp only [if_neg hm, mul_zero]

theorem reflectedFellerHeatSeries_pairing (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (m : ℕ) (t : ℝ) (ht : 0 < t) :
    reflectedFellerPairing L hL (neumannCosine L m) (reflectedFellerHeatSeries L hL D f t) =
      Real.exp (-reflectedFellerHeatRate L D * (m : ℝ) ^ 2 * t) *
        reflectedFellerPairing L hL (neumannCosine L m) f := by
  rw [reflectedFellerHeatSeries, map_add, map_smul, smul_eq_mul, reflectedFellerPairing_cosine_one,
    (reflectedFellerPairing L hL (neumannCosine L m)).map_tsum
      (reflectedFellerHeatTerm_summable L hL D hD f t ht)]
  simp_rw [reflectedFellerHeatTerm_pairing]
  cases m with
  | zero =>
    simp only [Nat.cast_zero, neumannCosine_zero, reflectedFellerPairing_apply, one_mul,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, Real.exp_zero, if_true, mul_one,
      Nat.zero_ne_add_one, if_false, tsum_zero, add_zero]
  | succ k =>
    simp only [Nat.succ_ne_zero, if_false, mul_zero, zero_add,
      Nat.add_right_cancel_iff, tsum_ite_eq']

theorem reflectedFellerHeatSeries_eq (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ) (ht : 0 < t) :
    reflectedFellerHeatSeries L hL D f t = reflectedFellerTimeOperator L hL D t f := by
  apply reflectedFeller_cosine_pairings_separate L hL
  intro n
  rw [reflectedFellerHeatSeries_pairing L hL D hD f n t ht,
    reflectedFellerPairing_cosine_time L hL D hD.le n f t ht.le]
  have he : -reflectedFellerHeatRate L D * (n : ℝ) ^ 2 * t =
      -D * ((n : ℝ) * Real.pi / L) ^ 2 * t := by
    unfold reflectedFellerHeatRate
    ring
  rw [he]

end TimeTraps.Probability
