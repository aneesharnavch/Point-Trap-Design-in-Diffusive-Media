module

public import TimeTraps.Probability.BrownianOccupationL1TimeKernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

@[expose] public section

/-! Positive-time Gaussian absolute continuity makes the joint time/path
evaluation map nonsingular with respect to Lebesgue measure. Consequently
arbitrary scalar L1 representatives compose measurably, and their absolute
occupation time is jointly integrable on every finite horizon. -/

namespace TimeTraps.Probability

open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_time_eval_quasiMeasurePreserving (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    QuasiMeasurePreserving (fun p : ℝ × Ω => B p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod P) volume := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply QuasiMeasurePreserving.prod_of_right
    (hjoint.comp ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  refine ⟨?_, ?_⟩
  · change Measurable (fun ω => B s.toNNReal ω)
    exact hjoint.comp
      ((measurable_const : Measurable (fun _ : Ω => s.toNNReal)).prodMk measurable_id)
  change P.map (B s.toNNReal) ≪ volume
  rw [(hB.hasLaw_eval s.toNNReal).map_eq]
  exact gaussianReal_absolutelyContinuous 0 (Real.toNNReal_pos.mpr hs.1).ne'

theorem brownian_time_L1_aestronglyMeasurable (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g) :
    AEStronglyMeasurable (fun p : ℝ × Ω => g (B p.1.toNNReal p.2))
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod P) :=
  hg.aestronglyMeasurable.comp_quasiMeasurePreserving
    (brownian_time_eval_quasiMeasurePreserving hB hjoint T)

theorem brownian_time_L1_integrable (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun p : ℝ × Ω => g (B p.1.toNNReal p.2))
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hm := brownian_time_L1_aestronglyMeasurable hB hjoint T hg
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact brownian_eval_L1_integrable hB hg (Real.toNNReal_pos.mpr hs.1)
  · have hi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
      (brownianOccupationL1Majorant_intervalIntegrable T.val)).mul_const (∫ x, |g x|)
    apply hi.mono' hm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [Real.norm_eq_abs]
    rw [brownianOccupationL1Majorant_eq_peak hs.1.le]
    have hb := brownian_eval_L1_abs_bound hB hg (Real.toNNReal_pos.mpr hs.1)
    simpa only [Real.coe_toNNReal s hs.1.le] using hb

theorem brownian_time_L1_intervalIntegrable_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g) :
    ∀ᵐ ω ∂P, IntervalIntegrable (fun s => g (B s.toNNReal ω)) volume 0 T.val := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  filter_upwards [(brownian_time_L1_integrable hB hjoint T hg).prod_left_ae] with ω hω
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr hω

end TimeTraps.Probability
