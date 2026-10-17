module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentError
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentPath
public import TimeTraps.Probability.ReflectedInteriorLocalTimeRandomHorizon

@[expose] public section

/-! The actual local-time paths satisfy the quantitative compact-time
spatial fourth-moment estimate. The continuous path representative is
measurable; the same estimate holds for the literal original supremum. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedSpatialFourthConstant (L D : ℝ) (T : ℝ≥0) : ℝ :=
  reflectedSpatialFourthCorrectionConstant L D T / (Real.sqrt (2 * D) ^ 2) ^ 4

theorem reflectedSpatialFourthConstant_nonneg (L : ℝ) {D : ℝ} (hD : 0 < D) (T : ℝ≥0) :
    0 ≤ reflectedSpatialFourthConstant L D T :=
  div_nonneg (reflectedSpatialFourthCorrectionConstant_nonneg L hD T) (by positivity)

theorem reflectedLocalTimeCompactPath_sub_bound_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      ‖reflectedLocalTimeCompactPath L hL D hD x T a.val ω -
        reflectedLocalTimeCompactPath L hL D hD x T b.val ω‖ ≤
      reflectedInteriorLevelError L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a b ω /
        Real.sqrt (2 * D) ^ 2 := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  filter_upwards [reflectedInteriorOccupation_level_compact_bound_ae L hL x hσ T a b,
    reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a.val,
    reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L b.val] with ω hbnd ha hb
  apply (reflectedLocalTimeCompactPath L hL D hD x T a.val ω -
    reflectedLocalTimeCompactPath L hL D hD x T b.val ω).norm_le_of_nonempty.mpr
  intro t
  rw [ContinuousMap.sub_apply, reflectedLocalTimeCompactPath_apply L hL D hD x T a.val ha,
    reflectedLocalTimeCompactPath_apply L hL D hD x T b.val hb, Real.norm_eq_abs]
  exact hbnd t.val t.property.2

theorem reflectedLocalTimeCompactPath_sub_memLp_four (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    MemLp (fun ω => reflectedLocalTimeCompactPath L hL D hD x T a.val ω -
      reflectedLocalTimeCompactPath L hL D hD x T b.val ω) 4 brownianDyadicMeasure := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hM : MemLp (fun ω => reflectedInteriorLevelError L hL x hσ T a b ω / Real.sqrt (2 * D) ^ 2)
      4 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using
      (reflectedInteriorLevelError_memLp_four L hL D hD x T a b).mul_const (Real.sqrt (2 * D) ^ 2)⁻¹
  exact hM.mono'
    ((reflectedLocalTimeCompactPath_stronglyMeasurable L hL D hD x T a.val).sub
      (reflectedLocalTimeCompactPath_stronglyMeasurable L hL D hD x T b.val)).aestronglyMeasurable
    (reflectedLocalTimeCompactPath_sub_bound_ae L hL D hD x T a b)

theorem reflectedLocalTimeCompactPath_spatial_fourth_moment (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    (∫ ω, ‖reflectedLocalTimeCompactPath L hL D hD x T a.val ω -
      reflectedLocalTimeCompactPath L hL D hD x T b.val ω‖ ^ 4 ∂brownianDyadicMeasure) ≤
      reflectedSpatialFourthConstant L D T * |a.val - b.val| ^ 2 := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hM : MemLp (fun ω => reflectedInteriorLevelError L hL x hσ T a b ω / Real.sqrt (2 * D) ^ 2)
      4 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using
      (reflectedInteriorLevelError_memLp_four L hL D hD x T a b).mul_const (Real.sqrt (2 * D) ^ 2)⁻¹
  calc
    _ ≤ ∫ ω, (reflectedInteriorLevelError L hL x hσ T a b ω / Real.sqrt (2 * D) ^ 2) ^ 4
        ∂brownianDyadicMeasure := by
      apply integral_mono_ae (brownian_memLp_four_integrable_fourth
        (reflectedLocalTimeCompactPath_sub_memLp_four L hL D hD x T a b).norm)
        (brownian_memLp_four_integrable_fourth hM)
      filter_upwards [reflectedLocalTimeCompactPath_sub_bound_ae L hL D hD x T a b] with ω hb
      exact pow_le_pow_left₀ (norm_nonneg _) hb 4
    _ = (∫ ω, reflectedInteriorLevelError L hL x hσ T a b ω ^ 4 ∂brownianDyadicMeasure) /
        (Real.sqrt (2 * D) ^ 2) ^ 4 := by
      simp only [div_eq_mul_inv, mul_pow, inv_pow, integral_mul_const]
    _ ≤ (reflectedSpatialFourthCorrectionConstant L D T * |a.val - b.val| ^ 2) /
        (Real.sqrt (2 * D) ^ 2) ^ 4 :=
      div_le_div_of_nonneg_right (reflectedInteriorLevelError_fourth_spatial_bound L hL D hD x T a b)
        (by positivity)
    _ = _ := by unfold reflectedSpatialFourthConstant; ring

theorem reflectedInteriorOccupation_sup_difference_memLp_four (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    MemLp (fun ω => ⨆ t : BrownianCompactTime T,
      |reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L b.val t.val ω|)
      4 brownianDyadicMeasure :=
  (reflectedLocalTimeCompactPath_sub_memLp_four L hL D hD x T a b).norm.ae_eq
    (reflectedLocalTimeCompactPath_sub_norm_ae L hL D hD x T a.val b.val)

theorem reflectedInteriorOccupation_compact_spatial_fourth_moment (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    (∫ ω, (⨆ t : BrownianCompactTime T,
      |reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L b.val t.val ω|) ^ 4
      ∂brownianDyadicMeasure) ≤
      reflectedSpatialFourthConstant L D T * |a.val - b.val| ^ 2 := by
  have he := integral_congr_ae
    ((reflectedLocalTimeCompactPath_sub_norm_ae L hL D hD x T a.val b.val).mono
      (fun _ h => congrArg (fun z : ℝ => z ^ 4) h))
  rw [← he]
  exact reflectedLocalTimeCompactPath_spatial_fourth_moment L hL D hD x T a b

end TimeTraps.Probability
