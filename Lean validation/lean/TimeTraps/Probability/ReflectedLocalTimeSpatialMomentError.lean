module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentMaximal

@[expose] public section

/-! The all-time Tanaka error majorant has a quantitative fourth moment.
The constant is explicit and independent of the two interior levels and
of the particle's initial state. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedSpatialFourthCorrectionConstant (L D : ℝ) (T : ℝ≥0) : ℝ :=
  128 * L ^ 2 + 1228800 * Real.sqrt (2 * D) ^ 4 * reflectedSpatialSecondConstant L D T

theorem reflectedSpatialFourthCorrectionConstant_nonneg (L : ℝ) {D : ℝ} (hD : 0 < D) (T : ℝ≥0) :
    0 ≤ reflectedSpatialFourthCorrectionConstant L D T := by
  have hK := reflectedSpatialSecondConstant_nonneg L hD T
  unfold reflectedSpatialFourthCorrectionConstant
  positivity

theorem reflectedInteriorLevelError_memLp_four (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    MemLp (reflectedInteriorLevelError L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a b)
      4 brownianDyadicMeasure :=
  (memLp_const (2 * |a.val - b.val|)).add
    (reflectedInteriorKinkCompact_fourth_energy L hL D hD x T a b).1

theorem reflectedInteriorLevelError_fourth_spatial_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a b : Ioo (0 : ℝ) L) :
    (∫ ω, reflectedInteriorLevelError L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity))
      T a b ω ^ 4 ∂brownianDyadicMeasure) ≤
      reflectedSpatialFourthCorrectionConstant L D T * |a.val - b.val| ^ 2 := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  let N := fun ω => ‖brownianIntegralContinuousL2 T
    (reflectedInteriorLevelIntegrand L hL x hσ T a - reflectedInteriorLevelIntegrand L hL x hσ T b) ω‖
  have hiN : Integrable (fun ω => N ω ^ 4) brownianDyadicMeasure :=
    brownian_memLp_four_integrable_fourth (reflectedInteriorKinkCompact_fourth_energy L hL D hD x T a b).1
  have hd : |a.val - b.val| ≤ L := abs_le.mpr ⟨by linarith [a.property.1, b.property.2],
    by linarith [a.property.2, b.property.1]⟩
  have hd2 := (sq_le_sq₀ (abs_nonneg (a.val - b.val)) hL.le).mpr hd
  have hd4 : |a.val - b.val| ^ 4 ≤ L ^ 2 * |a.val - b.val| ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hd2 (sq_nonneg |a.val - b.val|)]
  calc
    _ ≤ ∫ ω, 8 * ((2 * |a.val - b.val|) ^ 4 + N ω ^ 4) ∂brownianDyadicMeasure := by
      apply integral_mono (brownian_memLp_four_integrable_fourth
        (reflectedInteriorLevelError_memLp_four L hL D hD x T a b))
        (((integrable_const _).add hiN).const_mul _)
      intro ω
      have hN : 0 ≤ N ω := norm_nonneg _
      have h := add_pow_le (by positivity : 0 ≤ 2 * |a.val - b.val|) hN 4
      norm_num only [show (4 : ℕ) - 1 = 3 by norm_num, show (2 : ℝ) ^ 3 = 8 by norm_num] at h
      exact h
    _ = 8 * ((2 * |a.val - b.val|) ^ 4 + ∫ ω, N ω ^ 4 ∂brownianDyadicMeasure) := by
      rw [integral_const_mul, integral_add (integrable_const _) hiN]
      simp
    _ ≤ 8 * ((2 * |a.val - b.val|) ^ 4 +
        153600 * Real.sqrt (2 * D) ^ 4 * reflectedSpatialSecondConstant L D T * |a.val - b.val| ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_right
        (reflectedInteriorKinkCompact_fourth_spatial_bound L hL D hD x T a b) _) (by norm_num)
    _ ≤ _ := by
      unfold reflectedSpatialFourthCorrectionConstant
      nlinarith

end TimeTraps.Probability
