module

public import TimeTraps.Probability.BrownianLocalTimeMeasure

@[expose] public section

/-! A countable rational-interval event yields equality of the actual
spatial local-time density measure and the actual Brownian occupation
measure. The event is independent of every later test function. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianLocalTimeLevelMeasure_Ioo_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (p q : ℚ) :
    ∀ᵐ ω ∂P, brownianLocalTimeLevelMeasure hB hBm hjoint T ω (Ioo p q) =
      brownianOccupationMeasure B T ω (Ioo p q) := by
  let g : ℝ → ℝ := (Ioo (p : ℝ) (q : ℝ)).indicator (fun _ => 1)
  have hg : Integrable g volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const measure_Ioo_lt_top.ne)
  filter_upwards [brownianLocalTimeLevelVersion_spatial_integrable_ae hB hBm hjoint T hg,
    brownianLocalTimeLevelVersion_occupation_L1_ae hB hBm hjoint T hg] with ω hi he
  rw [brownianLocalTimeLevelMeasure, withDensity_ofReal_apply_indicator
    (fun a => brownianLocalTimeLevelVersion_nonneg hB hBm hjoint T a ω) measurableSet_Ioo hi,
    brownianOccupationMeasure, finite_map_apply_ofReal_indicator
      (brownianOccupationMeasure_path_measurable hjoint ω) measurableSet_Ioo]
  apply congrArg ENNReal.ofReal
  erw [intervalIntegral.integral_of_le T.coe_nonneg] at he
  exact he

def brownianLocalTimeMeasureRegular (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (ω : Ω) : Prop :=
  ∀ p q : ℚ, brownianLocalTimeLevelMeasure hB hBm hjoint T ω (Ioo p q) =
    brownianOccupationMeasure B T ω (Ioo p q)

theorem brownianLocalTimeMeasureRegular_measurableSet (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MeasurableSet {ω | brownianLocalTimeMeasureRegular hB hBm hjoint T ω} := by
  simp only [brownianLocalTimeMeasureRegular, ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun q => measurableSet_eq_fun
    (brownianLocalTimeLevelMeasure_apply_measurable hB hBm hjoint T (s := Ioo (p : ℝ) q) measurableSet_Ioo)
    (brownianOccupationMeasure_apply_measurable hjoint T measurableSet_Ioo)))

theorem brownianLocalTimeMeasureRegular_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, brownianLocalTimeMeasureRegular hB hBm hjoint T ω :=
  ae_all_iff.mpr (fun p => ae_all_iff.mpr (fun q => brownianLocalTimeLevelMeasure_Ioo_ae hB hBm hjoint T p q))

theorem brownianLocalTimeMeasureRegular_measure_eq {hB : IsPreBrownianReal B P}
    {hBm : ∀ t, Measurable (B t)}
    {hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)} {T : ℝ≥0} {ω : Ω}
    (hω : brownianLocalTimeMeasureRegular hB hBm hjoint T ω) :
    brownianLocalTimeLevelMeasure hB hBm hjoint T ω = brownianOccupationMeasure B T ω := by
  have : IsFiniteMeasure (brownianOccupationMeasure B T ω) := brownianOccupationMeasure_finite B T ω
  exact (Real.measure_ext_Ioo_rat (fun p q => (hω p q).symm)).symm

theorem brownianLocalTimeMeasureRegular_mass {hB : IsPreBrownianReal B P}
    {hBm : ∀ t, Measurable (B t)}
    {hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)} {T : ℝ≥0} {ω : Ω}
    (hω : brownianLocalTimeMeasureRegular hB hBm hjoint T ω) :
    brownianLocalTimeLevelMeasure hB hBm hjoint T ω univ = ENNReal.ofReal T.val := by
  rw [brownianLocalTimeMeasureRegular_measure_eq hω]
  exact brownianOccupationMeasure_univ hjoint T ω

theorem brownianLocalTimeMeasureRegular_integrable {hB : IsPreBrownianReal B P}
    {hBm : ∀ t, Measurable (B t)}
    {hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)} {T : ℝ≥0} {ω : Ω}
    (hω : brownianLocalTimeMeasureRegular hB hBm hjoint T ω) :
    Integrable (fun a => brownianLocalTimeLevelVersion hB hBm hjoint T a ω) volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (brownianLocalTimeLevelVersion_jointlyMeasurable hB hBm hjoint T).of_uncurry_right.aestronglyMeasurable
    (Eventually.of_forall (fun a => brownianLocalTimeLevelVersion_nonneg hB hBm hjoint T a ω))).mp
  have hm := brownianLocalTimeMeasureRegular_mass hω
  simp only [brownianLocalTimeLevelMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
  rw [hm]
  exact ENNReal.ofReal_ne_top

theorem brownianLocalTimeMeasureRegular_integral {hB : IsPreBrownianReal B P}
    {hBm : ∀ t, Measurable (B t)}
    {hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)} {T : ℝ≥0} {ω : Ω}
    (hω : brownianLocalTimeMeasureRegular hB hBm hjoint T ω) :
    (∫ a, brownianLocalTimeLevelVersion hB hBm hjoint T a ω) = T.val := by
  apply ENNReal.ofReal_eq_ofReal_iff (integral_nonneg
    (fun a => brownianLocalTimeLevelVersion_nonneg hB hBm hjoint T a ω)) T.coe_nonneg |>.mp
  rw [ofReal_integral_eq_lintegral_ofReal (brownianLocalTimeMeasureRegular_integrable hω)
    (Eventually.of_forall (fun a => brownianLocalTimeLevelVersion_nonneg hB hBm hjoint T a ω))]
  have hm := brownianLocalTimeMeasureRegular_mass hω
  dsimp only [brownianLocalTimeLevelMeasure] at hm
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
  exact hm

end TimeTraps.Probability
