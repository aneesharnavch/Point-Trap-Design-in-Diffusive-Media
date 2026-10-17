module

public import TimeTraps.Analysis.DensityMapIntervals
public import TimeTraps.Probability.BrownianLocalTimeOccupationL1

@[expose] public section

/-! The actual spatial density measure and the actual pushforward of
time measure on (0,T]. Their evaluations on measurable sets are
measurable in the sample. Finiteness of the time measure is independent
of any occupation identity. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianOccupationMeasure (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) T.val)).map (fun s => B s.toNNReal ω)

def brownianLocalTimeLevelMeasure (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (ω : Ω) : Measure ℝ :=
  volume.withDensity (fun a => ENNReal.ofReal (brownianLocalTimeLevelVersion hB hBm hjoint T a ω))

theorem brownianOccupationMeasure_path_measurable
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (ω : Ω) :
    Measurable (fun s : ℝ => B s.toNNReal ω) :=
  hjoint.of_uncurry_right.comp measurable_real_toNNReal

theorem brownianOccupationMeasure_finite (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    IsFiniteMeasure (brownianOccupationMeasure B T ω) :=
  Measure.isFiniteMeasure_map _ _

theorem brownianOccupationMeasure_univ
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (ω : Ω) :
    brownianOccupationMeasure B T ω univ = ENNReal.ofReal T.val := by
  rw [brownianOccupationMeasure, Measure.map_apply (brownianOccupationMeasure_path_measurable hjoint ω)
    MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero]

theorem brownianOccupationMeasure_apply_measurable
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable (fun ω => brownianOccupationMeasure B T ω s) := by
  have hm : Measurable (fun p : ℝ × Ω => B p.1.toNNReal p.2) :=
    hjoint.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have he : (fun ω => brownianOccupationMeasure B T ω s) =
      (fun ω => ENNReal.ofReal (∫ t, s.indicator (fun _ => (1 : ℝ)) (B t.toNNReal ω)
        ∂volume.restrict (Ioc (0 : ℝ) T.val))) := by
    funext ω
    exact finite_map_apply_ofReal_indicator (brownianOccupationMeasure_path_measurable hjoint ω) hs
  rw [he]
  exact (((measurable_const.indicator hs).comp hm).stronglyMeasurable.integral_prod_left').measurable.ennreal_ofReal

theorem brownianLocalTimeLevelMeasure_measurable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (brownianLocalTimeLevelMeasure hB hBm hjoint T) :=
  measurable_withDensity (((brownianLocalTimeLevelVersion_jointlyMeasurable hB hBm hjoint T).comp
    measurable_swap).ennreal_ofReal)

theorem brownianLocalTimeLevelMeasure_apply_measurable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable (fun ω => brownianLocalTimeLevelMeasure hB hBm hjoint T ω s) :=
  (Measure.measurable_coe hs).comp (brownianLocalTimeLevelMeasure_measurable hB hBm hjoint T)

end TimeTraps.Probability

end
