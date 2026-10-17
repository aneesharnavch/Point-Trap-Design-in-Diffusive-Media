module

public import TimeTraps.Probability.BrownianLocalTimeTimeRegularity
public import TimeTraps.Probability.BrownianLocalTimeMeasureTests

@[expose] public section

/-! At each fixed horizon, the jointly measurable continuous-time field
agrees with the spatial local-time version almost everywhere in level and
sample. Fubini gives equality of the actual density measures almost surely.
This does not assert agreement at all levels on a common event. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem brownianLocalTimeTimeField_levelVersion_ae (a : ℝ) (T : ℝ≥0) :
    brownianLocalTimeTimeField a T =ᵐ[brownianDyadicMeasure]
      brownianDyadicLocalTimeLevelVersion T a :=
  (brownianLocalTimeTimeField_compensation_ae a T).trans
    (brownianLocalTimeLevelVersion_ae brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable T a).symm

theorem brownianLocalTimeTimeField_levelVersion_prod_ae (T : ℝ≥0) :
    (fun p : ℝ × (ℕ → ℝ) => brownianLocalTimeTimeField p.1 T p.2) =ᵐ[volume.prod brownianDyadicMeasure]
      (fun p => brownianDyadicLocalTimeLevelVersion T p.1 p.2) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (brownianLocalTimeTimeField_timeSlice_measurable T)
    (brownianDyadicLocalTimeLevelVersion_jointlyMeasurable T))).mpr
  exact Eventually.of_forall (fun a => brownianLocalTimeTimeField_levelVersion_ae a T)

theorem brownianLocalTimeTimeField_levelVersion_sections_ae (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, (fun a => brownianLocalTimeTimeField a T ω) =ᵐ[volume]
      (fun a => brownianDyadicLocalTimeLevelVersion T a ω) := by
  apply (Measure.ae_ae_comm (μ := volume) (ν := brownianDyadicMeasure)
    (p := fun a ω => brownianLocalTimeTimeField a T ω = brownianDyadicLocalTimeLevelVersion T a ω)
    (measurableSet_eq_fun
    (brownianLocalTimeTimeField_timeSlice_measurable T)
    (brownianDyadicLocalTimeLevelVersion_jointlyMeasurable T))).mp
  exact Measure.ae_ae_of_ae_prod (brownianLocalTimeTimeField_levelVersion_prod_ae T)

def brownianLocalTimeTimeMeasure (T : ℝ≥0) (ω : ℕ → ℝ) : Measure ℝ :=
  volume.withDensity (fun a => ENNReal.ofReal (brownianLocalTimeTimeField a T ω))

theorem brownianLocalTimeTimeMeasure_measurable (T : ℝ≥0) :
    Measurable (brownianLocalTimeTimeMeasure T) :=
  measurable_withDensity (((brownianLocalTimeTimeField_timeSlice_measurable T).comp
    measurable_swap).ennreal_ofReal)

theorem brownianLocalTimeTimeMeasure_apply_measurable (T : ℝ≥0) {s : Set ℝ}
    (hs : MeasurableSet s) : Measurable (fun ω => brownianLocalTimeTimeMeasure T ω s) :=
  (Measure.measurable_coe hs).comp (brownianLocalTimeTimeMeasure_measurable T)

theorem brownianLocalTimeTimeMeasure_levelMeasure_ae (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianLocalTimeTimeMeasure T ω =
      brownianLocalTimeLevelMeasure brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable T ω := by
  filter_upwards [brownianLocalTimeTimeField_levelVersion_sections_ae T] with ω he
  apply withDensity_congr_ae
  exact he.fun_comp ENNReal.ofReal

theorem brownianLocalTimeTimeMeasure_eq_ae (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      brownianLocalTimeTimeMeasure T ω = brownianOccupationMeasure brownianDyadicPath T ω := by
  filter_upwards [brownianLocalTimeTimeMeasure_levelMeasure_ae T,
    brownianLocalTimeLevelMeasure_eq_ae brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable T] with ω he ho
  exact he.trans ho

end TimeTraps.Probability

end
