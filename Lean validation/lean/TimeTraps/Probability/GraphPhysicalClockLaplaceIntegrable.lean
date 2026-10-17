module

public import TimeTraps.Probability.GraphPhysicalClockLaplaceMeasurable
public import TimeTraps.Probability.GraphBorelResolventData

@[expose] public section

/-! Both time/path Laplace integrands are absolutely integrable. The
reference-clock bound uses the proved positive lower speed and finite
upper speed, not continuity of the speed at vertices. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.physicalPathLaplace_product_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    {f : GraphRealization P.geometry → ℝ} (hf : Measurable f)
    {C q : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (hq : 0 < q) :
    Integrable (fun z : ℝ × GraphContinuousPath P.geometry => Real.exp (-q * z.1) *
      f (P.geometry.physicalPath b hb z.2 z.1.toNNReal))
      ((volume.restrict (Ioi (0 : ℝ))).prod (P.continuousPathLaw h0 x)) := by
  let inst := P.continuousPathLaw_probability h0 x
  have he : IntegrableOn (fun r : ℝ => Real.exp (-q * r)) (Ioi 0) := by
    simpa only [sub_zero] using reflectedDiscounted_exponential_integrable hq (0 : ℝ)
  apply ((he.mul_const C).comp_fst (P.continuousPathLaw h0 x)).mono'
    (P.geometry.physicalPathLaplace_jointlyMeasurable b hb hf q).aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le

theorem GraphShiftedContactOperatorProblem.physicalClockLaplace_product_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry)
    {f : GraphRealization P.geometry → ℝ} (hf : Measurable f)
    {C q : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) (hq : 0 < q) :
    Integrable (fun z : ℝ × GraphContinuousPath P.geometry =>
      Real.exp (-q * (P.geometry.physicalClock b hb z.1.toNNReal z.2 : ℝ)) *
        f (z.2 z.1.toNNReal) * P.geometry.physicalSpeed b (z.2 z.1.toNNReal))
      ((volume.restrict (Ioi (0 : ℝ))).prod (P.continuousPathLaw h0 x)) := by
  let inst := P.continuousPathLaw_probability h0 x
  let m : ℝ := P.geometry.physicalSpeedLower b hb
  let B : ℝ := P.geometry.physicalSpeedUpper b hb
  have hm : 0 < m := P.geometry.physicalSpeedLower_pos b hb
  have hC0 : 0 ≤ C := (norm_nonneg (f x)).trans (hC x)
  have he : IntegrableOn (fun r : ℝ => Real.exp (-(q * m) * r)) (Ioi 0) := by
    simpa only [sub_zero] using reflectedDiscounted_exponential_integrable (mul_pos hq hm) (0 : ℝ)
  apply ((he.mul_const (C * B)).comp_fst (P.continuousPathLaw h0 x)).mono'
    (P.geometry.physicalClockLaplace_jointlyMeasurable b hb hf q).aestronglyMeasurable
  have ht : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod (P.continuousPathLaw h0 x)), 0 < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ht] with z hz
  have hlo : m * z.1 ≤ (P.geometry.physicalClock b hb z.1.toNNReal z.2 : ℝ) := by
    have hh := (P.geometry.physicalClock_bounds b hb z.1.toNNReal z.2).1
    change m * (z.1.toNNReal : ℝ) ≤ (P.geometry.physicalClock b hb z.1.toNNReal z.2 : ℝ) at hh
    simpa only [Real.coe_toNNReal z.1 hz.le] using hh
  have hrho : 0 < P.geometry.physicalSpeed b (z.2 z.1.toNNReal) :=
    hm.trans_le (P.geometry.physicalSpeed_bound b hb _).1
  have hexp : Real.exp (-q * (P.geometry.physicalClock b hb z.1.toNNReal z.2 : ℝ)) ≤
      Real.exp (-(q * m) * z.1) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hrho.le]
  calc
    _ ≤ Real.exp (-q * (P.geometry.physicalClock b hb z.1.toNNReal z.2 : ℝ)) * C *
        P.geometry.physicalSpeed b (z.2 z.1.toNNReal) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le) hrho.le
    _ ≤ Real.exp (-q * (P.geometry.physicalClock b hb z.1.toNNReal z.2 : ℝ)) * C * B :=
      mul_le_mul_of_nonneg_left (P.geometry.physicalSpeed_bound b hb _).2
        (mul_nonneg (Real.exp_pos _).le hC0)
    _ ≤ Real.exp (-(q * m) * z.1) * (C * B) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hexp (mul_nonneg hC0 (NNReal.coe_nonneg _))

end TimeTraps.Analysis
