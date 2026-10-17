module

public import TimeTraps.Probability.ReflectedFellerDecayBounds

@[expose] public section

/-! Uniform exponential convergence of the actual reflected Feller
evolution to its physical spatial mean. The prefactor three is explicit,
not asserted optimal; the exponent is the first Neumann frequency. -/

namespace TimeTraps.Probability

open Set Filter TimeTraps.Analysis
open scoped Topology

theorem reflectedFeller_decay (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f : C(Icc (0 : ℝ) L, ℝ))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖reflectedFellerTimeOperator L hL D t f - reflectedFellerMean L hL f • 1‖ ≤
      3 * Real.exp (-reflectedFellerHeatRate L D * t) * ‖reflectedFellerMeanZero L hL f‖ := by
  have hc : ‖reflectedFellerTimeOperator L hL D t f - reflectedFellerMean L hL f • 1‖ ≤
      ‖reflectedFellerMeanZero L hL f‖ := by
    rw [← reflectedFellerTimeOperator_center]
    exact reflectedFellerOperator_contraction L hL _ _
  by_cases hq : (1 : ℝ) / 3 ≤ Real.exp (-reflectedFellerHeatRate L D * t)
  · apply hc.trans
    nlinarith [mul_nonneg (norm_nonneg (reflectedFellerMeanZero L hL f))
      (show 0 ≤ 3 * Real.exp (-reflectedFellerHeatRate L D * t) - 1 by linarith)]
  · have ht' : 0 < t := by
      by_contra h
      have he : t = 0 := le_antisymm (not_lt.mp h) ht
      simp only [he, mul_zero, Real.exp_zero] at hq
      norm_num at hq
    have hq' := lt_of_not_ge hq
    have hd : 0 < 1 - Real.exp (-reflectedFellerHeatRate L D * t) := by linarith
    apply (reflectedFeller_decay_geometric L hL D hD f t ht').trans
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg
      (mul_nonneg (norm_nonneg (reflectedFellerMeanZero L hL f))
        (Real.exp_pos (-reflectedFellerHeatRate L D * t)).le)
      (show 0 ≤ 1 - 3 * Real.exp (-reflectedFellerHeatRate L D * t) by linarith)]

theorem reflectedFeller_decay_operator (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (t : ℝ) (ht : 0 ≤ t) :
    ‖(reflectedFellerTimeOperator L hL D t).comp (reflectedFellerMeanZero L hL)‖ ≤
      6 * Real.exp (-reflectedFellerHeatRate L D * t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖reflectedFellerTimeOperator L hL D t (reflectedFellerMeanZero L hL f)‖ ≤ _
  rw [reflectedFellerTimeOperator_center]
  have hm : ‖reflectedFellerMeanZero L hL f‖ ≤ 2 * ‖f‖ := by
    rw [reflectedFellerMeanZero_apply]
    calc
      _ ≤ ‖f‖ + ‖reflectedFellerMean L hL f • (1 : C(Icc (0 : ℝ) L, ℝ))‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + ‖f‖ := by
        apply add_le_add_right
        rw [norm_smul]
        have hone : ‖(1 : C(Icc (0 : ℝ) L, ℝ))‖ ≤ 1 := by
          exact (ContinuousMap.norm_le _ zero_le_one).mpr (fun _ => by simp)
        exact (mul_le_of_le_one_right (norm_nonneg _) hone).trans (reflectedFellerMean_norm L hL f)
      _ = _ := by ring
  calc
    _ ≤ 3 * Real.exp (-reflectedFellerHeatRate L D * t) * ‖reflectedFellerMeanZero L hL f‖ :=
      reflectedFeller_decay L hL D hD f t ht
    _ ≤ 3 * Real.exp (-reflectedFellerHeatRate L D * t) * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem reflectedFeller_tendsto_mean (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (f : C(Icc (0 : ℝ) L, ℝ)) :
    Tendsto (fun t : ℝ => reflectedFellerTimeOperator L hL D t f)
      atTop (𝓝 (reflectedFellerMean L hL f • 1)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-reflectedFellerHeatRate L D * t)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (reflectedFellerHeatRate_pos L hL D hD))
    simpa only [Function.comp_def, id_eq, neg_mul] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (Filter.eventually_atTop.2 ⟨0, fun t ht => reflectedFeller_decay L hL D hD f t ht⟩)
  simpa only [mul_zero, zero_mul] using (he.const_mul 3).mul_const ‖reflectedFellerMeanZero L hL f‖

end TimeTraps.Probability
