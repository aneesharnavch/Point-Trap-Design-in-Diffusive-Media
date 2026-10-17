module

public import TimeTraps.Probability.ReflectedLocalTimeBandErrorVersion
public import TimeTraps.Analysis.L2IntegralSectionsFinite
public import TimeTraps.Analysis.ContinuousBandAverage

@[expose] public section

/-! The ordinary spatial average of the jointly measurable maximal error
is an actual L2 random variable. Product integrability and its Bochner
representation are derived from continuity of the L2-valued family. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedBandErrorAverage (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) (ω : ℕ → ℝ) : ℝ :=
  (1 / (2 * h)) * ∫ b in Ioo (a.val - h) (a.val + h), reflectedBandErrorVersion L hL x hσ T a b ω

noncomputable def reflectedBandErrorAverageL2 (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) : Lp ℝ 2 brownianDyadicMeasure :=
  (1 / (2 * h)) • ∫ b in Ioo (a.val - h) (a.val + h), reflectedBandErrorL2 L hL x hσ T a b

theorem reflectedBandErrorL2_integrableOn (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) :
    IntegrableOn (reflectedBandErrorL2 L hL x hσ T a) (Ioo (a.val - h) (a.val + h)) volume :=
  ((reflectedBandErrorL2_continuous L hL x hσ T a).integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem reflectedBandErrorVersion_product_integrable (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => reflectedBandErrorVersion L hL x hσ T a p.1 p.2)
      ((volume.restrict (Ioo (a.val - h) (a.val + h))).prod brownianDyadicMeasure) :=
  real_L2_sections_integrable (reflectedBandErrorL2_integrableOn L hL x hσ T a h)
    (reflectedBandErrorVersion_jointlyMeasurable L hL x hσ T a).aestronglyMeasurable
    (fun b => (reflectedBandErrorVersion_ae L hL x hσ T a b).symm)

theorem reflectedBandErrorVersion_spatial_integrable_ae (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, IntegrableOn (fun b => reflectedBandErrorVersion L hL x hσ T a b ω)
      (Ioo (a.val - h) (a.val + h)) volume :=
  (reflectedBandErrorVersion_product_integrable L hL x hσ T a h).prod_left_ae

theorem reflectedBandErrorAverageL2_coe (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) :
    reflectedBandErrorAverageL2 L hL x hσ T a h =ᵐ[brownianDyadicMeasure]
      reflectedBandErrorAverage L hL x hσ T a h := by
  have hi := real_L2_integral_sections_ae (reflectedBandErrorL2_integrableOn L hL x hσ T a h)
    (reflectedBandErrorVersion_jointlyMeasurable L hL x hσ T a).aestronglyMeasurable
    (fun b => (reflectedBandErrorVersion_ae L hL x hσ T a b).symm)
  filter_upwards [Lp.coeFn_smul (1 / (2 * h))
    (∫ b in Ioo (a.val - h) (a.val + h), reflectedBandErrorL2 L hL x hσ T a b), hi] with ω hs hω
  change ((1 / (2 * h)) • (∫ b in Ioo (a.val - h) (a.val + h),
    reflectedBandErrorL2 L hL x hσ T a b : Lp ℝ 2 brownianDyadicMeasure)) ω = _
  rw [hs, Pi.smul_apply, smul_eq_mul, hω]
  rfl

theorem reflectedBandErrorAverage_memLp (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) :
    MemLp (reflectedBandErrorAverage L hL x hσ T a h) 2 brownianDyadicMeasure :=
  (Lp.memLp (reflectedBandErrorAverageL2 L hL x hσ T a h)).ae_eq
    (reflectedBandErrorAverageL2_coe L hL x hσ T a h)

theorem reflectedBandErrorAverage_measurable (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) :
    Measurable (reflectedBandErrorAverage L hL x hσ T a h) :=
  measurable_const.mul
    ((reflectedBandErrorVersion_jointlyMeasurable L hL x hσ T a).stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (Ioo (a.val - h) (a.val + h)))).measurable

end TimeTraps.Probability
