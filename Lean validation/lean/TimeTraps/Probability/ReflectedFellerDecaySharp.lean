module

public import TimeTraps.Probability.ReflectedFellerDecay

@[expose] public section

/-! The first physical Neumann mode attains the decay exponent. No
finite uniform prefactor can give a strictly larger exponential rate
for all continuous inputs. This is sharpness of the rate, not a claim
that the prefactor in the preceding uniform estimate is optimal. -/

namespace TimeTraps.Probability

open Set TimeTraps.Analysis

theorem reflectedFeller_cosine_norm (L : ℝ) (hL : 0 < L) (n : ℕ) :
    ‖neumannCosine L n‖ = 1 := by
  apply le_antisymm (reflectedFeller_cosine_norm_le_one L n)
  have h := (neumannCosine L n).norm_coe_le_norm ⟨0, le_rfl, hL.le⟩
  simpa only [neumannCosine, ContinuousMap.coe_mk, mul_zero, Real.cos_zero, norm_one] using h

theorem reflectedFeller_first_mode_decay (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (t : ℝ) (ht : 0 ≤ t) :
    ‖reflectedFellerTimeOperator L hL D t (neumannCosine L 1)‖ =
      Real.exp (-reflectedFellerHeatRate L D * t) := by
  change ‖reflectedFellerOperator L hL (Real.toNNReal (2 * D * t)) (neumannCosine L 1)‖ = _
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by simp,
    reflectedFellerOperator_cosine_time L hL D hD 1 t ht, norm_smul,
    Real.norm_of_nonneg (Real.exp_pos _).le, reflectedFeller_cosine_norm L hL 1, mul_one]
  congr 1
  unfold reflectedFellerHeatRate
  norm_num

theorem reflectedFeller_decay_rate_le (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (C r : ℝ)
    (hbound : ∀ (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ), 0 ≤ t →
      ‖reflectedFellerTimeOperator L hL D t f - reflectedFellerMean L hL f • 1‖ ≤
        C * Real.exp (-r * t) * ‖reflectedFellerMeanZero L hL f‖) :
    r ≤ reflectedFellerHeatRate L D := by
  have hb (t : ℝ) (ht : 0 ≤ t) :
      Real.exp (-reflectedFellerHeatRate L D * t) ≤ C * Real.exp (-r * t) := by
    have h := hbound (neumannCosine L 1) t ht
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by simp,
      reflectedFellerMean_cosine L hL 1 (by norm_num), zero_smul, sub_zero,
      reflectedFellerMeanZero_cosine L hL 1 (by norm_num),
      reflectedFeller_cosine_norm L hL 1, mul_one, Nat.cast_one,
      reflectedFeller_first_mode_decay L hL D hD.le t ht] at h
    exact h
  have hC : 1 ≤ C := by simpa only [mul_zero, Real.exp_zero, mul_one] using hb 0 le_rfl
  by_contra hr
  have hd : 0 < r - reflectedFellerHeatRate L D := sub_pos.mpr (lt_of_not_ge hr)
  let t := Real.log (C + 1) / (r - reflectedFellerHeatRate L D)
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg (by linarith)) hd.le
  have h := mul_le_mul_of_nonneg_right (hb t ht) (Real.exp_pos (r * t)).le
  have he : Real.exp (-reflectedFellerHeatRate L D * t) * Real.exp (r * t) = C + 1 := by
    rw [← Real.exp_add]
    have harg : -reflectedFellerHeatRate L D * t + r * t = Real.log (C + 1) := by
      dsimp [t]
      field_simp
      ring
    rw [harg, Real.exp_log (by linarith)]
  have hz : C * Real.exp (-r * t) * Real.exp (r * t) = C := by
    rw [mul_assoc, ← Real.exp_add]
    rw [show -r * t + r * t = 0 by ring, Real.exp_zero, mul_one]
  rw [he, hz] at h
  linarith

end TimeTraps.Probability
