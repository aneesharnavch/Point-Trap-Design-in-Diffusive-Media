module

public import TimeTraps.Analysis.GraphPhysicalClockIntegral
public import TimeTraps.Probability.KillingLifetimeTimeChangeIntegralData
public import TimeTraps.Probability.KillingLifetimeMeanMeasurable

@[expose] public section

/-! The extended lifetime under a bounded positive Borel speed is exactly
the original speed accumulated before that lifetime. Infinity is proved
using the strict positive lower speed bound, not discarded. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem borelSpeed_integral_before_top (v : GraphPhysicalClockSpeed) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (v.rate r.toNNReal)) = ⊤ := by
  have hl : (∫⁻ _r in Ioi (0 : ℝ), ENNReal.ofReal (v.lower : ℝ)) ≤
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (v.rate r.toNNReal) :=
    lintegral_mono (fun r => ENNReal.ofReal_le_ofReal (v.lower_le r.toNNReal))
  have he : (∫⁻ _r in Ioi (0 : ℝ), ENNReal.ofReal (v.lower : ℝ)) = ⊤ := by
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioi]
    exact ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr v.lower_pos)
  rw [he] at hl
  exact top_unique hl

theorem borelSpeed_lifetime_value (v : GraphPhysicalClockSpeed) {τ : WithTop ℝ} (hτ : 0 ≤ τ) :
    nonnegativeLifetimeValue (positiveClockLifetimeMap v.clock τ) =
      ∫⁻ r in positiveTimeBefore τ, ENNReal.ofReal (v.rate r.toNNReal) := by
  cases τ with
  | top =>
    have hs : positiveTimeBefore ⊤ = Ioi (0 : ℝ) := by
      ext r
      simp only [positiveTimeBefore, mem_ofPred_eq, WithTop.coe_lt_top, and_true, mem_Ioi]
    rw [positiveClockLifetimeMap_top, nonnegativeLifetimeValue_top, hs, borelSpeed_integral_before_top]
  | coe r =>
    have hr : 0 ≤ r := WithTop.coe_le_coe.mp hτ
    have hs : positiveTimeBefore (r : WithTop ℝ) = Ioo (0 : ℝ) r := by
      ext s
      simp only [positiveTimeBefore, mem_ofPred_eq, WithTop.coe_lt_coe, mem_Ioo]
    rw [positiveClockLifetimeMap_coe, nonnegativeLifetimeValue_coe, hs, v.clock_coe]
    change ENNReal.ofReal (∫ s in (0 : ℝ)..(r.toNNReal : ℝ), v.rate s.toNNReal) = _
    rw [Real.coe_toNNReal _ hr, intervalIntegral.integral_of_le hr, integral_Ioc_eq_integral_Ioo]
    exact ofReal_integral_eq_lintegral_ofReal
      ((v.rate_intervalIntegrable 0 r).1.mono_set Ioo_subset_Ioc_self)
      (Eventually.of_forall (fun s => (v.rate_pos s.toNNReal).le))

end TimeTraps.Probability
