module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountTail

@[expose] public section

/-! Exact splitting of a discounted clamped terminal expression. Only
actual absolute integrability of that expression is required; the tail
correction is then integrable by subtracting the exponential constant. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter

theorem graphPointDiscount_terminal_split {α t : ℝ} (hα : 0 < α) (ht : 0 ≤ t)
    (L U : ℝ → ℝ) (hU0 : U 0 = 0)
    (hG : IntegrableOn (fun H => Real.exp (-(α * H)) * (L (min t H) + U (H - min t H))) (Ioi 0)) :
    α * (∫ H in Ioi (0 : ℝ), Real.exp (-(α * H)) * (L (min t H) + U (H - min t H))) =
      α * (∫ H in (0 : ℝ)..t, Real.exp (-(α * H)) * L H) +
      Real.exp (-(α * t)) * L t +
      Real.exp (-(α * t)) * (α * ∫ s in Ioi (0 : ℝ), Real.exp (-(α * s)) * U s) := by
  let G : ℝ → ℝ := fun H => Real.exp (-(α * H)) * (L (min t H) + U (H - min t H))
  have hg : IntegrableOn G (Ioi t) := hG.mono_set (Ioi_subset_Ioi ht)
  have hc : IntegrableOn (fun H => Real.exp (-(α * H)) * L t) (Ioi t) := by
    simpa only [IntegrableOn, neg_mul] using (integrableOn_exp_mul_Ioi (a := -α) (neg_lt_zero.mpr hα) t).mul_const (L t)
  have htail : IntegrableOn (fun H => Real.exp (-(α * H)) * U (H - t)) (Ioi t) := by
    apply (hg.sub hc).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    dsimp only [G, Pi.sub_apply]
    rw [min_eq_left hH.le]
    ring
  have hpast : (∫ H in (0 : ℝ)..t, G H) = ∫ H in (0 : ℝ)..t, Real.exp (-(α * H)) * L H := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with H hH
    dsimp only [G]
    rw [min_eq_right hH.2, sub_self, hU0, add_zero]
  have hfuture : (∫ H in Ioi t, G H) =
      (∫ H in Ioi t, Real.exp (-(α * H)) * L t) +
      ∫ H in Ioi t, Real.exp (-(α * H)) * U (H - t) := by
    rw [← integral_add hc htail]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
    dsimp only [G, Pi.add_apply]
    rw [min_eq_left hH.le]
    ring
  change α * (∫ H in Ioi (0 : ℝ), G H) = _
  rw [← intervalIntegral.integral_interval_add_Ioi hG hg, hpast, hfuture,
    graphPointDiscount_tail_translate]
  have hcval := graphPointDiscount_tail_constant hα t (L t)
  nlinarith [hcval]

end TimeTraps.Probability
