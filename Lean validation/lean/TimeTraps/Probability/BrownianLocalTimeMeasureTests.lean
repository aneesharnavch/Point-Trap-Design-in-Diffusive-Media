module

public import TimeTraps.Probability.BrownianLocalTimeMeasureIdentity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! On the single rational-interval occupation event, the measure
identity transports every nonnegative measurable test, and every
bounded Borel real test, without a global spatial L¹ assumption.
The same event works for all such tests. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianLocalTimeMeasureRegular_lintegral {hB : IsPreBrownianReal B P}
    {hBm : ∀ t, Measurable (B t)}
    {hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)} {T : ℝ≥0} {ω : Ω}
    (hω : brownianLocalTimeMeasureRegular hB hBm hjoint T ω)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ a, g a * ENNReal.ofReal (brownianLocalTimeLevelVersion hB hBm hjoint T a ω)) =
      ∫⁻ s, g (B s.toNNReal ω) ∂volume.restrict (Ioc (0 : ℝ) T.val) := by
  have hw : Measurable (fun a => brownianLocalTimeLevelVersion hB hBm hjoint T a ω) :=
    Measurable.of_uncurry_right (f := brownianLocalTimeLevelVersion hB hBm hjoint T) (y := ω)
      (brownianLocalTimeLevelVersion_jointlyMeasurable hB hBm hjoint T)
  calc
    _ = ∫⁻ a, g a ∂brownianLocalTimeLevelMeasure hB hBm hjoint T ω := by
      rw [brownianLocalTimeLevelMeasure, lintegral_withDensity_eq_lintegral_mul _ hw.ennreal_ofReal hg]
      simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ a, g a ∂brownianOccupationMeasure B T ω := by
      rw [brownianLocalTimeMeasureRegular_measure_eq hω]
    _ = _ := lintegral_map hg (brownianOccupationMeasure_path_measurable hjoint ω)

theorem brownianLocalTimeMeasureRegular_bounded_occupation {hB : IsPreBrownianReal B P}
    {hBm : ∀ t, Measurable (B t)}
    {hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)} {T : ℝ≥0} {ω : Ω}
    (hω : brownianLocalTimeMeasureRegular hB hBm hjoint T ω)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ x, |g x| ≤ M) :
    Integrable (fun a => g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) volume ∧
      IntervalIntegrable (fun s => g (B s.toNNReal ω)) volume 0 T.val ∧
      (∫ a, g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) =
        ∫ s in (0 : ℝ)..T.val, g (B s.toNNReal ω) := by
  refine ⟨(brownianLocalTimeMeasureRegular_integrable hω).bdd_mul hg.aestronglyMeasurable
    (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a)),
    brownianItoDrift_bounded_intervalIntegrable hg hjoint hb T ω, ?_⟩
  have hw : Measurable (fun a => brownianLocalTimeLevelVersion hB hBm hjoint T a ω) :=
    Measurable.of_uncurry_right (f := brownianLocalTimeLevelVersion hB hBm hjoint T) (y := ω)
      (brownianLocalTimeLevelVersion_jointlyMeasurable hB hBm hjoint T)
  calc
    _ = ∫ a, g a ∂brownianLocalTimeLevelMeasure hB hBm hjoint T ω := by
      rw [brownianLocalTimeLevelMeasure, integral_withDensity_eq_integral_toReal_smul
        hw.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with a
      rw [ENNReal.toReal_ofReal (brownianLocalTimeLevelVersion_nonneg hB hBm hjoint T a ω), smul_eq_mul]
      exact mul_comm _ _
    _ = ∫ a, g a ∂brownianOccupationMeasure B T ω := by
      rw [brownianLocalTimeMeasureRegular_measure_eq hω]
    _ = ∫ s, g (B s.toNNReal ω) ∂volume.restrict (Ioc (0 : ℝ) T.val) :=
      integral_map (brownianOccupationMeasure_path_measurable hjoint ω).aemeasurable hg.aestronglyMeasurable
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem brownianLocalTimeLevelMeasure_eq_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, brownianLocalTimeLevelMeasure hB hBm hjoint T ω = brownianOccupationMeasure B T ω :=
  (brownianLocalTimeMeasureRegular_ae hB hBm hjoint T).mono
    (fun _ hω => brownianLocalTimeMeasureRegular_measure_eq hω)

theorem brownianDyadicLocalTimeLevelMeasure_eq_ae (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      volume.withDensity (fun a => ENNReal.ofReal (brownianDyadicLocalTimeLevelVersion T a ω)) =
        (volume.restrict (Ioc (0 : ℝ) T.val)).map (fun s => brownianDyadicPath s.toNNReal ω) :=
  brownianLocalTimeLevelMeasure_eq_ae brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T

end TimeTraps.Probability
