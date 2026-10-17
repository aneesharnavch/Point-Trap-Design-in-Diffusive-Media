module

public import TimeTraps.Probability.ReflectedItoC2Formula
public import TimeTraps.Probability.ReflectedC2ItoIntegrandPath
public import TimeTraps.Probability.ReflectedC2ItoDrift
public import TimeTraps.Probability.ReflectedFoldRegulatorPaths

@[expose] public section

/-! The reflected C² Itô identity on one event throughout a fixed finite
horizon. The stochastic term is the actual canonical continuous horizon
path; only its fixed-time identification with the completed integral is
used before passage from countably many dense times by continuity. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

theorem reflectedItoC2_continuous_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      F (foldedTrajectory L D x brownianDyadicPath t ω) - F (reflectedFold L x) =
        reflectedC2ItoHorizonPath hF L hL D hD x T t ω +
          D * reflectedC2ItoDrift F brownianDyadicPath L D x t ω +
          deriv F 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
          deriv F L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω := by
  have ht (t : BrownianCompactTime T) :
      ∀ᵐ ω ∂brownianDyadicMeasure,
        F (foldedTrajectory L D x brownianDyadicPath t.val ω) - F (reflectedFold L x) =
          reflectedC2ItoHorizonPath hF L hL D hD x T t.val ω +
            D * reflectedC2ItoDrift F brownianDyadicPath L D x t.val ω +
            deriv F 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t.val ω -
            deriv F L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t.val ω := by
    filter_upwards [reflectedItoC2_formula hF L hL D hD x t.val,
      reflectedC2ItoHorizonPath_integral_ae hF L hL D hD x T t.val] with ω hf hi
    rw [min_eq_left t.property.2] at hi
    rw [← hi] at hf
    exact hf
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      F (foldedTrajectory L D x brownianDyadicPath (denseSeq (BrownianCompactTime T) n).val ω) -
          F (reflectedFold L x) =
        reflectedC2ItoHorizonPath hF L hL D hD x T (denseSeq (BrownianCompactTime T) n).val ω +
          D * reflectedC2ItoDrift F brownianDyadicPath L D x (denseSeq (BrownianCompactTime T) n).val ω +
          deriv F 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L
            (denseSeq (BrownianCompactTime T) n).val ω -
          deriv F L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L
            (denseSeq (BrownianCompactTime T) n).val ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime T) n))
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hD)
  filter_upwards [hall,
    reflectedC2ItoDrift_continuous_ae hF brownianDyadicPath_isBrownianReal L hL D x,
    reflectedFoldRegulatorPaths_ae x hσ hL] with ω he hd hr
  have hx : Continuous (fun t : ℝ≥0 => foldedTrajectory L D x brownianDyadicPath t ω) :=
    hr.path_continuous
  have hleft := (hF.continuous.comp hx).sub (continuous_const (y := F (reflectedFold L x)))
  have hright : Continuous (fun t : ℝ≥0 =>
      reflectedC2ItoHorizonPath hF L hL D hD x T t ω +
        D * reflectedC2ItoDrift F brownianDyadicPath L D x t ω +
        deriv F 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
        deriv F L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω) :=
    (((reflectedC2ItoHorizonPath_continuous hF L hL D hD x T ω).add
      (continuous_const.mul hd)).add (continuous_const.mul hr.lower_continuous)).sub
        (continuous_const.mul hr.upper_continuous)
  have heq := (denseRange_denseSeq (BrownianCompactTime T)).equalizer
    (hleft.comp continuous_subtype_val) (hright.comp continuous_subtype_val) (funext he)
  exact fun t ht => congrFun heq ⟨t, zero_le, ht⟩

theorem reflectedItoC2_continuous_initial_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (hx : x ∈ Icc 0 L) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      F (foldedTrajectory L D x brownianDyadicPath t ω) - F x =
        reflectedC2ItoHorizonPath hF L hL D hD x T t ω +
          D * reflectedC2ItoDrift F brownianDyadicPath L D x t ω +
          deriv F 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
          deriv F L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω := by
  simpa only [reflectedFold_eq_self L hL x hx] using
    reflectedItoC2_continuous_ae hF L hL D hD x T

end TimeTraps.Probability
