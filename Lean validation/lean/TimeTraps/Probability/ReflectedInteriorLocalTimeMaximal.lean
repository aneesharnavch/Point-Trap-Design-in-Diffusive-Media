module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeLevelL2
public import TimeTraps.Probability.ReflectedInteriorLocalTimeMaximalData

@[expose] public section

/-! A measurable square-integrable bound for the spatial increment of
the actual reflected interior correction, simultaneously at every time
in a compact horizon. The bound tends to zero in L2 with the level. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedInteriorLevelIntegrand (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) : BrownianIntegrand :=
  reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL a.val a.property x hσ T

noncomputable def reflectedInteriorLevelError (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) (ω : ℕ → ℝ) : ℝ :=
  2 * |a.val - b.val| + ‖brownianIntegralContinuousL2 T
    (reflectedInteriorLevelIntegrand L hL x hσ T a - reflectedInteriorLevelIntegrand L hL x hσ T b) ω‖

theorem reflectedInteriorLevelError_measurable (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    Measurable (reflectedInteriorLevelError L hL x hσ T a b) :=
  measurable_const.add (Lp.stronglyMeasurable _).norm.measurable

theorem reflectedInteriorLevelError_memLp (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    MemLp (reflectedInteriorLevelError L hL x hσ T a b) 2 brownianDyadicMeasure :=
  (memLp_const (2 * |a.val - b.val|)).add (brownianIntegralCompactNorm_memLp _ T)

theorem reflectedInteriorLevelError_bound_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |reflectedInteriorCorrection x σ L a.val t ω - reflectedInteriorCorrection x σ L b.val t ω| ≤
        reflectedInteriorLevelError L hL x hσ T a b ω :=
  reflectedInteriorCorrection_level_compact_bound_ae L hL a.val b.val a.property b.property x hσ T

theorem reflectedInteriorLevelError_L2norm_le (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    ‖(reflectedInteriorLevelError_memLp L hL x hσ T a b).toLp
      (reflectedInteriorLevelError L hL x hσ T a b)‖ ≤
      2 * |a.val - b.val| + 2 *
        ‖reflectedInteriorLevelIntegrand L hL x hσ T a - reflectedInteriorLevelIntegrand L hL x hσ T b‖ := by
  let f := reflectedInteriorLevelIntegrand L hL x hσ T a - reflectedInteriorLevelIntegrand L hL x hσ T b
  have hc : MemLp (fun _ : ℕ → ℝ => 2 * |a.val - b.val|) 2 brownianDyadicMeasure := memLp_const _
  have hn := brownianIntegralCompactNorm_memLp f T
  have hcn : ‖hc.toLp (fun _ : ℕ → ℝ => 2 * |a.val - b.val|)‖ ≤ 2 * |a.val - b.val| := by
    have hb : ∀ᵐ ω ∂brownianDyadicMeasure,
        ‖hc.toLp (fun _ : ℕ → ℝ => 2 * |a.val - b.val|) ω‖ ≤ 2 * |a.val - b.val| := by
      filter_upwards [hc.coeFn_toLp] with ω hω
      rw [hω, Real.norm_of_nonneg (by positivity)]
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by positivity : 0 ≤ 2 * |a.val - b.val|) hb
  change ‖(hc.add hn).toLp ((fun _ => 2 * |a.val - b.val|) +
    (fun ω => ‖brownianIntegralContinuousL2 T f ω‖))‖ ≤ _
  rw [hc.toLp_add hn]
  exact (norm_add_le _ _).trans (add_le_add hcn
    ((brownianIntegralCompactNorm_L2norm f T).trans_le (brownianIntegralContinuousL2_bound T f)))

theorem reflectedInteriorLevelError_L2norm_tendsto_zero (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0)
    {u : ℕ → Ioo (0 : ℝ) L} {a : Ioo (0 : ℝ) L} (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => ‖(reflectedInteriorLevelError_memLp L hL x hσ T (u n) a).toLp
      (reflectedInteriorLevelError L hL x hσ T (u n) a)‖) atTop (𝓝 0) := by
  have hK : Tendsto (fun n => reflectedInteriorLevelIntegrand L hL x hσ T (u n)) atTop
      (𝓝 (reflectedInteriorLevelIntegrand L hL x hσ T a)) :=
    (reflectedInteriorKinkIntegrand_level_continuous brownianDyadicPath_isBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ T).continuousAt.tendsto.comp hu
  have hv : Tendsto (fun n => (u n).val) atTop (𝓝 a.val) := continuous_subtype_val.tendsto a |>.comp hu
  have hb : Tendsto (fun n => 2 * |(u n).val - a.val| + 2 *
      ‖reflectedInteriorLevelIntegrand L hL x hσ T (u n) - reflectedInteriorLevelIntegrand L hL x hσ T a‖)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, norm_zero, mul_zero, add_zero] using
      ((hv.sub_const a.val).abs.const_mul (2 : ℝ)).add
        ((hK.sub_const (reflectedInteriorLevelIntegrand L hL x hσ T a)).norm.const_mul (2 : ℝ))
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => reflectedInteriorLevelError_L2norm_le L hL x hσ T (u n) a) hb

theorem reflectedInteriorLevelError_square_tendsto_zero (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0)
    {u : ℕ → Ioo (0 : ℝ) L} {a : Ioo (0 : ℝ) L} (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => ∫ ω, reflectedInteriorLevelError L hL x hσ T (u n) a ω ^ 2
      ∂brownianDyadicMeasure) atTop (𝓝 0) := by
  simpa only [memLp_norm_toLp_sq, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (reflectedInteriorLevelError_L2norm_tendsto_zero L hL x hσ T hu).pow 2

end TimeTraps.Probability
