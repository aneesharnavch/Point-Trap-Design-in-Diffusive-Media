module

public import TimeTraps.Probability.BrownianIntegralPastMultiplierApproximation
public import TimeTraps.Probability.ReflectedC2ItoIntegrand
public import TimeTraps.Probability.ReflectedItoFiniteDecomposition

@[expose] public section

/-! The actual finite driver sums in the reflected Taylor decomposition
are L² classes converging to the already constructed original-Brownian
C² integrand integral. The driver remains normalized; sqrt(2D) appears
once outside its weighted increments. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedC2ItoDriverSumL2 {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (n : ℕ) :
    Lp ℝ 2 brownianDyadicMeasure :=
  Real.sqrt (2 * D) • brownianIntegral brownianDyadicPath_isPreBrownianReal
    (brownianAdaptedContinuousProductStep brownianDyadicPath_measurable
      (reflectedC2DerivativeProcess_stronglyAdapted hF brownianDyadicPath_measurable L D x)
      (reflectedC2DerivativeProcess_bound hF brownianDyadicPath L hL D x) T n
      (brownianDyadicFoldSlopeIntegrand L hL x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T))

theorem reflectedC2ItoDriverSumL2_ae {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (n : ℕ) :
    reflectedC2ItoDriverSumL2 hF L hL D hD x T n =ᵐ[brownianDyadicMeasure]
      affineBrownianFoldDriverWeightedSum L hL x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) (deriv F) T n := by
  let hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)
  let A := brownianDyadicFoldSlopeIntegrand L hL x hσ T
  let H := reflectedC2DerivativeProcess F brownianDyadicPath L D x
  let hH := reflectedC2DerivativeProcess_stronglyAdapted hF brownianDyadicPath_measurable L D x
  let hb := reflectedC2DerivativeProcess_bound hF brownianDyadicPath L hL D x
  let U := brownianAdaptedContinuousProductStep brownianDyadicPath_measurable hH hb T n A
  have he := brownianPastStepIntegrand_integral_ae brownianDyadicPath_isPreBrownianReal
    (brownianDyadicGrid T n) (brownianDyadicGrid_monotone T n)
    (fun i => H (brownianDyadicGrid T n i.castSucc))
    (fun i => hH (brownianDyadicGrid T n i.castSucc))
    (fun i => hb (brownianDyadicGrid T n i.castSucc)) A
  change brownianIntegral brownianDyadicPath_isPreBrownianReal U =ᵐ[brownianDyadicMeasure]
    brownianStepIntegral
      (fun t ω => brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t A ω)
      (brownianDyadicGrid T n) (fun i => H (brownianDyadicGrid T n i.castSucc)) at he
  have hW (t : ℝ≥0) (ht : t ≤ T) :
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t A =ᵐ[brownianDyadicMeasure]
        brownianFoldSlopeGlobalPath L hL x hσ t := by
    have hp := (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t).symm
    change brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t
      (brownianFoldSlopeIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL x hσ T) =ᵐ[brownianDyadicMeasure] _
    rw [brownianFoldSlopeIntegral_upTo, min_eq_left ht]
    exact hp
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : Fin (2 ^ n + 1),
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal (brownianDyadicGrid T n i) A ω =
        brownianFoldSlopeGlobalPath L hL x hσ (brownianDyadicGrid T n i) ω :=
    ae_all_iff.mpr (fun i => hW _ (brownianDyadicGrid_mem_Icc T n i).2)
  change (Real.sqrt (2 * D) • brownianIntegral brownianDyadicPath_isPreBrownianReal U :
    Lp ℝ 2 brownianDyadicMeasure) =ᵐ[brownianDyadicMeasure] _
  filter_upwards [Lp.coeFn_smul (Real.sqrt (2 * D))
    (brownianIntegral brownianDyadicPath_isPreBrownianReal U), he, hall] with ω hs he hω
  rw [hs, Pi.smul_apply, smul_eq_mul, he]
  change Real.sqrt (2 * D) * (∑ i : Fin (2 ^ n), H (brownianDyadicGrid T n i.castSucc) ω *
    (brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal (brownianDyadicGrid T n i.succ) A ω -
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal (brownianDyadicGrid T n i.castSucc) A ω)) = _
  simp_rw [hω]
  rfl

theorem reflectedC2ItoDriverSumL2_tendsto {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    Tendsto (reflectedC2ItoDriverSumL2 hF L hL D hD x T) atTop
      (𝓝 (reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL D hD x T)) := by
  let hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)
  let A := brownianDyadicFoldSlopeIntegrand L hL x hσ T
  have hA : brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure T A = A := by
    change brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure T
      (brownianFoldSlopeIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL x hσ T) = _
    rw [brownianFoldSlopeIntegrand_cutoff, min_self]
    rfl
  have h := brownianAdaptedContinuousProductStepIntegral_tendsto brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable
    (reflectedC2DerivativeProcess_stronglyAdapted hF brownianDyadicPath_measurable L D x)
    (reflectedC2DerivativeProcess_jointlyMeasurable hF brownianDyadicPath_jointly_measurable L D x)
    (reflectedC2DerivativeProcess_bound hF brownianDyadicPath L hL D x)
    (reflectedC2DerivativeProcess_continuous_ae hF brownianDyadicPath_isBrownianReal L D x) T A hA
  have hs := h.const_smul (Real.sqrt (2 * D))
  change Tendsto (reflectedC2ItoDriverSumL2 hF L hL D hD x T) atTop
    (𝓝 (Real.sqrt (2 * D) • brownianIntegral brownianDyadicPath_isPreBrownianReal
      (reflectedC2ItoMultiplier hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL D x A))) at hs
  have ht : reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL D hD x T =
      Real.sqrt (2 * D) • brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedC2ItoMultiplier hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
          brownianDyadicPath_jointly_measurable L hL D x A) := by
    change brownianIntegral brownianDyadicPath_isPreBrownianReal (Real.sqrt (2 * D) • _) = _
    rw [map_smul]
    rfl
  rw [ht]
  exact hs

end TimeTraps.Probability

end
