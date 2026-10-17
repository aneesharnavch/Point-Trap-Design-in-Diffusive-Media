module

public import TimeTraps.Probability.GraphBorelResolventData

@[expose] public section

/-! Raw adapted discounted occupation prefixes for bounded Borel tests.
Joint measurability of clamped particle observations is proved before
composition with the Borel test, so no test continuity is required. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.borelDiscountedPast
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (α : ℝ) (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  ∫ r in (0 : ℝ)..(t : ℝ), Real.exp (-α * r) * f (p r.toNNReal)

omit [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.borelDiscountedPast_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) (α : ℝ) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.borelDiscountedPast f α) := by
  intro t
  have he : P.borelDiscountedPast f α t = (fun p : GraphContinuousPath P.geometry =>
      ∫ r in Ioc (0 : ℝ) (t : ℝ), Real.exp (-α * r) * f (p (min t r.toNNReal))) := by
    funext p
    rw [borelDiscountedPast, intervalIntegral.integral_of_le t.coe_nonneg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [min_eq_right (Real.toNNReal_le_iff_le_coe.mpr hr.2)]
  rw [he]
  let : MeasurableSpace (GraphContinuousPath P.geometry) := graphContinuousNaturalFiltration P.geometry t
  have hX : StronglyMeasurable (fun q : ℝ × GraphContinuousPath P.geometry => q.2 (min t q.1.toNNReal)) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun (r : ℝ) (p : GraphContinuousPath P.geometry) => p (min t r.toNNReal))
    · intro p
      exact p.continuous.comp (continuous_const.min continuous_real_toNNReal)
    · intro r
      exact (graphContinuousPath_past_measurable P.geometry (min_le_left t r.toNNReal)).stronglyMeasurable
  have he : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => Real.exp (-α * q.1)) := by fun_prop
  exact (he.mul (hf.comp hX.measurable)).stronglyMeasurable.integral_prod_left'

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.borelDiscountedPast_norm_le
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphRealization P.geometry → ℝ)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C) {α : ℝ} (hα : 0 ≤ α)
    (t : ℝ≥0) (p : GraphContinuousPath P.geometry) : ‖P.borelDiscountedPast f α t p‖ ≤ (t : ℝ) * C := by
  have hb : ∀ r ∈ Set.uIoc (0 : ℝ) (t : ℝ), ‖Real.exp (-α * r) * f (p r.toNNReal)‖ ≤ C := by
    intro r hr
    rw [uIoc_of_le t.coe_nonneg] at hr
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-α * r) * C := mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by nlinarith [hr.1.le])) hC0
      _ = C := one_mul C
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [borelDiscountedPast, sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm] using hi

theorem GraphShiftedContactOperatorProblem.borelDiscountedPast_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ) (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C) {α : ℝ} (hα : 0 ≤ α) (t : ℝ≥0) :
    Integrable (P.borelDiscountedPast f α t) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (integrable_const ((t : ℝ) * C)).mono'
    (((P.borelDiscountedPast_stronglyAdapted f hf α t).mono
      ((graphContinuousNaturalFiltration P.geometry).le t)).aestronglyMeasurable)
    (Eventually.of_forall (P.borelDiscountedPast_norm_le f hC0 hC hα t))

end TimeTraps.Analysis
