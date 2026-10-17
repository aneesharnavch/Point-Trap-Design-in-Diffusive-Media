module

public import TimeTraps.Probability.BrownianLocalTimeSignTime
public import TimeTraps.Probability.BrownianLocalTimeDifferenceTime

@[expose] public section

/-! The actual Tanaka compensation has a uniform square-root time
modulus in L2. Combined with its proved level continuity, this gives
joint continuity in level and time, without a sample-path assertion. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaCompensation_time_norm_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (S T : ℝ≥0) :
    ‖brownianTanakaCompensation hB hBm hjoint a T - brownianTanakaCompensation hB hBm hjoint a S‖ ≤
      2 * Real.sqrt |T.val - S.val| := by
  let U := brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T)
  let V := brownianTanakaDifferenceL2 B a S (brownianTanakaDifference_memLp hB a S)
  let I := brownianSignIntegral hB hBm hjoint a T
  let J := brownianSignIntegral hB hBm hjoint a S
  change ‖(U - I) - (V - J)‖ ≤ _
  rw [show (U - I) - (V - J) = (U - V) - (I - J) by abel]
  calc
    _ ≤ ‖U - V‖ + ‖I - J‖ := norm_sub_le _ _
    _ ≤ Real.sqrt |T.val - S.val| + Real.sqrt |T.val - S.val| :=
      add_le_add (brownianTanakaDifferenceL2_time_norm_le hB a S T)
        (brownianSignIntegral_time_norm hB hBm hjoint a S T).le
    _ = _ := by ring

theorem brownianTanakaCompensation_joint_continuous (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ≥0 => brownianTanakaCompensation hB hBm hjoint p.1 p.2) := by
  let C := brownianTanakaCompensation hB hBm hjoint
  apply continuous_iff_seqContinuous.mpr
  intro u p hu
  have ht : Tendsto (fun n => (u n).2.val) atTop (𝓝 p.2.val) :=
    continuous_subtype_val.continuousAt.tendsto.comp ((continuous_snd.tendsto p).comp hu)
  have htime : Tendsto (fun n => 2 * Real.sqrt |(u n).2.val - p.2.val|) atTop (𝓝 0) := by
    have hr := Real.continuous_sqrt.continuousAt.tendsto.comp (ht.sub_const p.2.val).abs
    simpa only [Function.comp_def, sub_self, abs_zero, Real.sqrt_zero, mul_zero] using hr.const_mul 2
  have hlevel : Tendsto (fun n => ‖C (u n).1 p.2 - C p.1 p.2‖) atTop (𝓝 0) := by
    have hl := (brownianTanakaCompensation_level_continuous hB hBm hjoint p.2).continuousAt.tendsto.comp ((continuous_fst.tendsto p).comp hu)
    simpa only [Function.comp_def, C, sub_self, norm_zero] using (hl.sub_const (C p.1 p.2)).norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => show ‖C (u n).1 (u n).2 - C p.1 p.2‖ ≤
      2 * Real.sqrt |(u n).2.val - p.2.val| + ‖C (u n).1 p.2 - C p.1 p.2‖ from ?_)
    (by simpa only [zero_add] using htime.add hlevel)
  calc
    _ ≤ ‖C (u n).1 (u n).2 - C (u n).1 p.2‖ + ‖C (u n).1 p.2 - C p.1 p.2‖ := by
      simpa only [dist_eq_norm] using dist_triangle (C (u n).1 (u n).2) (C (u n).1 p.2) (C p.1 p.2)
    _ ≤ _ := add_le_add (brownianTanakaCompensation_time_norm_le hB hBm hjoint (u n).1 p.2 (u n).2) le_rfl

theorem brownianTanakaCompensation_time_continuous (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) :
    Continuous (brownianTanakaCompensation hB hBm hjoint a) :=
  (brownianTanakaCompensation_joint_continuous hB hBm hjoint).comp
    (continuous_const.prodMk continuous_id)

theorem brownianDyadicTanakaCompensation_joint_continuous :
    Continuous (fun p : ℝ × ℝ≥0 => brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable p.1 p.2) :=
  brownianTanakaCompensation_joint_continuous brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable

end TimeTraps.Probability
