module

public import TimeTraps.Probability.ReflectedFellerSeriesIdentification

@[expose] public section

/-! Quantitative decay of the actual reflected Feller evolution in the
continuous-function norm. The mean is the normalized physical spatial
integral. The positive-time estimate sums the proved cosine heat series
against a geometric majorant; it does not assume initial differentiability. -/

namespace TimeTraps.Probability

open Set TimeTraps.Analysis

theorem reflectedFellerTimeOperator_center (L : ℝ) (hL : 0 < L)
    (D t : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerTimeOperator L hL D t (reflectedFellerMeanZero L hL f) =
      reflectedFellerTimeOperator L hL D t f - reflectedFellerMean L hL f • 1 := by
  rw [reflectedFellerMeanZero_apply, map_sub, map_smul]
  change _ - _ • reflectedFellerOperator L hL (Real.toNNReal (2 * D * t)) 1 = _
  rw [reflectedFellerOperator_one]

theorem reflectedFellerHeatTerm_geometric_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f : C(Icc (0 : ℝ) L, ℝ))
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖reflectedFellerHeatTerm L hL D f n t‖ ≤
      (2 * ‖f‖ * Real.exp (-reflectedFellerHeatRate L D * t)) *
        Real.exp (-reflectedFellerHeatRate L D * t) ^ n := by
  have hc : 0 ≤ reflectedFellerHeatRate L D * t :=
    mul_nonneg (reflectedFellerHeatRate_pos L hL D hD).le ht
  have hn : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [pow_two]
    exact_mod_cast Nat.le_mul_self (n + 1)
  calc
    _ ≤ 2 * ‖f‖ * Real.exp
        (-reflectedFellerHeatRate L D * ((n + 1 : ℕ) : ℝ) ^ 2 * t) :=
      reflectedFellerHeatTerm_norm L hL D f n t
    _ ≤ 2 * ‖f‖ * Real.exp (((n + 1 : ℕ) : ℝ) *
        (-reflectedFellerHeatRate L D * t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hn hc]
    _ = _ := by rw [Real.exp_nat_mul, pow_succ]; ring

theorem reflectedFeller_decay_geometric (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f : C(Icc (0 : ℝ) L, ℝ))
    (t : ℝ) (ht : 0 < t) :
    ‖reflectedFellerTimeOperator L hL D t f - reflectedFellerMean L hL f • 1‖ ≤
      (2 * ‖reflectedFellerMeanZero L hL f‖ * Real.exp (-reflectedFellerHeatRate L D * t)) /
        (1 - Real.exp (-reflectedFellerHeatRate L D * t)) := by
  let g := reflectedFellerMeanZero L hL f
  let q := Real.exp (-reflectedFellerHeatRate L D * t)
  have hq₀ : 0 ≤ q := (Real.exp_pos _).le
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (reflectedFellerHeatRate_pos L hL D hD)) ht)
  have hs : Summable (fun n : ℕ => (2 * ‖g‖ * q) * q ^ n) :=
    (summable_geometric_of_lt_one hq₀ hq₁).mul_left _
  have hb : ∀ n : ℕ, ‖reflectedFellerHeatTerm L hL D g n t‖ ≤ (2 * ‖g‖ * q) * q ^ n :=
    fun n => reflectedFellerHeatTerm_geometric_bound L hL D hD g n t ht.le
  have hn := hs.of_nonneg_of_le (fun n => norm_nonneg _) hb
  have hmean : reflectedFellerMean L hL g = 0 := by
    change reflectedFellerMean L hL (f - reflectedFellerMean L hL f • 1) = 0
    rw [map_sub, map_smul, reflectedFellerMean_one, smul_eq_mul, mul_one, sub_self]
  rw [← reflectedFellerTimeOperator_center, ← reflectedFellerHeatSeries_eq L hL D hD g t ht]
  rw [reflectedFellerHeatSeries, hmean, zero_smul, zero_add]
  calc
    _ ≤ ∑' n : ℕ, ‖reflectedFellerHeatTerm L hL D g n t‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (2 * ‖g‖ * q) * q ^ n := hn.tsum_le_tsum hb hs
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁]
      rfl

end TimeTraps.Probability
