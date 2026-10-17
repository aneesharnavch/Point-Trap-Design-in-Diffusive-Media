module

public import TimeTraps.Probability.BrownianLocalTimeBandData

@[expose] public section

/-! The all-L1 occupation identity identifies the independently defined
occupation band with the true Bochner average of nearby L2 compensations.
The open band and the interval integral agree because Lebesgue endpoints
have zero measure, with no assumption on spatial sample continuity. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaLevelIntegral_band (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) {h : ℝ}
    (hh : 0 ≤ h) (T : ℝ≥0) :
    brownianTanakaLevelIntegral hB hBm hjoint T (brownianBandIndicator a h) =
      ∫ x in (a - h)..(a + h), brownianTanakaCompensation hB hBm hjoint x T := by
  let C := fun x => brownianTanakaCompensation hB hBm hjoint x T
  have he : (fun x => brownianBandIndicator a h x • C x) =
      (Ioo (a - h) (a + h)).indicator C := by
    funext x
    by_cases hx : x ∈ Ioo (a - h) (a + h)
    · simp only [brownianBandIndicator, indicator_of_mem hx, one_smul]
    · simp only [brownianBandIndicator, indicator_of_notMem hx, zero_smul]
  change (∫ x, brownianBandIndicator a h x • C x) = ∫ x in (a - h)..(a + h), C x
  rw [he, integral_indicator measurableSet_Ioo,
    intervalIntegral.integral_of_le (by linarith : a - h ≤ a + h), integral_Ioc_eq_integral_Ioo]

theorem brownianBandOccupationL2_eq_average (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) {h : ℝ}
    (hh : 0 ≤ h) (T : ℝ≥0) :
    brownianBandOccupationL2 hB hjoint a h T =
      (1 / (2 * h)) • ∫ x in (a - h)..(a + h), brownianTanakaCompensation hB hBm hjoint x T := by
  unfold brownianBandOccupationL2
  rw [← brownianTanakaLevelIntegral_eq_occupationL1 hB hBm hjoint T
    (brownianBandIndicator_integrable a h), brownianTanakaLevelIntegral_band hB hBm hjoint a hh T]

end TimeTraps.Probability
