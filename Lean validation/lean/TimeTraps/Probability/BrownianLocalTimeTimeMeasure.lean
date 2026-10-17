module

public import TimeTraps.Probability.BrownianLocalTimeTimeMeasureTransfer

@[expose] public section

/-! The actual continuous-time local-time field is an occupation density
at each fixed horizon, on one measurable full-probability event independent
of the test function. This yields spatial integrability, exact total mass,
and transport of all nonnegative measurable and bounded Borel tests.
No spatial continuity or simultaneous regularity at every level is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

def brownianLocalTimeTimeMeasureRegular (T : ℝ≥0) (ω : ℕ → ℝ) : Prop :=
  ∀ p q : ℚ, brownianLocalTimeTimeMeasure T ω (Ioo p q) =
    brownianOccupationMeasure brownianDyadicPath T ω (Ioo p q)

theorem brownianLocalTimeTimeMeasureRegular_measurableSet (T : ℝ≥0) :
    MeasurableSet {ω | brownianLocalTimeTimeMeasureRegular T ω} := by
  simp only [brownianLocalTimeTimeMeasureRegular, ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun q => measurableSet_eq_fun
    (brownianLocalTimeTimeMeasure_apply_measurable T (s := Ioo (p : ℝ) q) measurableSet_Ioo)
    (brownianOccupationMeasure_apply_measurable brownianDyadicPath_jointly_measurable T measurableSet_Ioo)))

theorem brownianLocalTimeTimeMeasureRegular_ae (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianLocalTimeTimeMeasureRegular T ω := by
  filter_upwards [brownianLocalTimeTimeMeasure_eq_ae T] with ω he
  intro p q
  rw [he]

theorem brownianLocalTimeTimeMeasureRegular_measure_eq {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    brownianLocalTimeTimeMeasure T ω = brownianOccupationMeasure brownianDyadicPath T ω := by
  have : IsFiniteMeasure (brownianOccupationMeasure brownianDyadicPath T ω) :=
    brownianOccupationMeasure_finite brownianDyadicPath T ω
  exact (Real.measure_ext_Ioo_rat (fun p q => (hω p q).symm)).symm

theorem brownianLocalTimeTimeMeasureRegular_mass {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    brownianLocalTimeTimeMeasure T ω univ = ENNReal.ofReal T.val := by
  rw [brownianLocalTimeTimeMeasureRegular_measure_eq hω]
  exact brownianOccupationMeasure_univ brownianDyadicPath_jointly_measurable T ω

theorem brownianLocalTimeTimeMeasureRegular_integrable {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    Integrable (fun a => brownianLocalTimeTimeField a T ω) volume := by
  have hw : Measurable (fun a => brownianLocalTimeTimeField a T ω) :=
    Measurable.of_uncurry_right (f := fun a ω => brownianLocalTimeTimeField a T ω) (y := ω)
      (brownianLocalTimeTimeField_timeSlice_measurable T)
  apply (lintegral_ofReal_ne_top_iff_integrable hw.aestronglyMeasurable
    (Eventually.of_forall (fun a => brownianLocalTimeTimeField_nonneg a T ω))).mp
  have hm := brownianLocalTimeTimeMeasureRegular_mass hω
  dsimp only [brownianLocalTimeTimeMeasure] at hm
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
  rw [hm]
  exact ENNReal.ofReal_ne_top

theorem brownianLocalTimeTimeMeasureRegular_integral {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) :
    (∫ a, brownianLocalTimeTimeField a T ω) = T.val := by
  apply ENNReal.ofReal_eq_ofReal_iff (integral_nonneg
    (fun a => brownianLocalTimeTimeField_nonneg a T ω)) T.coe_nonneg |>.mp
  rw [ofReal_integral_eq_lintegral_ofReal (brownianLocalTimeTimeMeasureRegular_integrable hω)
    (Eventually.of_forall (fun a => brownianLocalTimeTimeField_nonneg a T ω))]
  have hm := brownianLocalTimeTimeMeasureRegular_mass hω
  dsimp only [brownianLocalTimeTimeMeasure] at hm
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
  exact hm

theorem brownianLocalTimeTimeMeasureRegular_lintegral {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ a, g a * ENNReal.ofReal (brownianLocalTimeTimeField a T ω)) =
      ∫⁻ s, g (brownianDyadicPath s.toNNReal ω) ∂volume.restrict (Ioc (0 : ℝ) T.val) := by
  have hw : Measurable (fun a => brownianLocalTimeTimeField a T ω) :=
    Measurable.of_uncurry_right (f := fun a ω => brownianLocalTimeTimeField a T ω) (y := ω)
      (brownianLocalTimeTimeField_timeSlice_measurable T)
  calc
    _ = ∫⁻ a, g a ∂brownianLocalTimeTimeMeasure T ω := by
      rw [brownianLocalTimeTimeMeasure, lintegral_withDensity_eq_lintegral_mul _ hw.ennreal_ofReal hg]
      simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ a, g a ∂brownianOccupationMeasure brownianDyadicPath T ω := by
      rw [brownianLocalTimeTimeMeasureRegular_measure_eq hω]
    _ = _ := lintegral_map hg
      (brownianOccupationMeasure_path_measurable brownianDyadicPath_jointly_measurable ω)

theorem brownianLocalTimeTimeMeasureRegular_bounded_occupation {T : ℝ≥0} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeTimeMeasureRegular T ω) {g : ℝ → ℝ}
    (hg : Measurable g) {M : ℝ} (hb : ∀ x, |g x| ≤ M) :
    Integrable (fun a => g a * brownianLocalTimeTimeField a T ω) volume ∧
      IntervalIntegrable (fun s => g (brownianDyadicPath s.toNNReal ω)) volume 0 T.val ∧
      (∫ a, g a * brownianLocalTimeTimeField a T ω) =
        ∫ s in (0 : ℝ)..T.val, g (brownianDyadicPath s.toNNReal ω) := by
  refine ⟨(brownianLocalTimeTimeMeasureRegular_integrable hω).bdd_mul hg.aestronglyMeasurable
    (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a)),
    brownianItoDrift_bounded_intervalIntegrable hg brownianDyadicPath_jointly_measurable hb T ω, ?_⟩
  have hw : Measurable (fun a => brownianLocalTimeTimeField a T ω) :=
    Measurable.of_uncurry_right (f := fun a ω => brownianLocalTimeTimeField a T ω) (y := ω)
      (brownianLocalTimeTimeField_timeSlice_measurable T)
  calc
    _ = ∫ a, g a ∂brownianLocalTimeTimeMeasure T ω := by
      rw [brownianLocalTimeTimeMeasure, integral_withDensity_eq_integral_toReal_smul
        hw.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with a
      rw [ENNReal.toReal_ofReal (brownianLocalTimeTimeField_nonneg a T ω), smul_eq_mul]
      exact mul_comm _ _
    _ = ∫ a, g a ∂brownianOccupationMeasure brownianDyadicPath T ω := by
      rw [brownianLocalTimeTimeMeasureRegular_measure_eq hω]
    _ = ∫ s, g (brownianDyadicPath s.toNNReal ω) ∂volume.restrict (Ioc (0 : ℝ) T.val) :=
      integral_map (brownianOccupationMeasure_path_measurable
        brownianDyadicPath_jointly_measurable ω).aemeasurable hg.aestronglyMeasurable
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

end TimeTraps.Probability
