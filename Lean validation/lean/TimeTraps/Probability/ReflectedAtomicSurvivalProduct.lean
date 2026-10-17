module

public import TimeTraps.Probability.ReflectedAtomicSurvivalStieltjes
public import TimeTraps.Probability.ReflectedAtomicSurvivalMultiplier
public import TimeTraps.Probability.BrownianStieltjesProduct

@[expose] public section

/-! The literal survival weight times an actual continuous Brownian
integral satisfies the stochastic product identity. Its finite-variation
term is the genuine integral of survival times the driver against the
actual atomic hazard measure. No killing representation is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicSurvival_stieltjes_product_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (f : BrownianIntegrand)
    (hf : brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure T f = f) :
    (fun ω => reflectedAtomicSurvival L D x a κ T ω * brownianIntegralGlobalPath f T ω -
      reflectedAtomicSurvival L D x a κ 0 ω * brownianIntegralGlobalPath f 0 ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ f) ω -
        ∫ r in Ioc (0 : ℝ) T.val, brownianIntegralGlobalPath f r.toNNReal ω
          ∂(reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω).measure) := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  have hHK : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      reflectedAtomicSurvival L D x a κ t ω =
        1 - reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ ω t.val := by
    filter_upwards [hall] with ω hω t
    rw [reflectedAtomicSurvivalLossStieltjes_apply_nnreal L hL D hD x a κ hκ hω t]
    ring
  exact brownianIntegralGlobalPath_stieltjes_product_ae (M := 1)
    (reflectedAtomicSurvival_raw_aestronglyMeasurable L D x a κ)
    (reflectedAtomicSurvival_jointlyMeasurable L D x a κ)
    (fun t ω => by
      rw [abs_of_pos (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).1]
      exact (reflectedAtomicSurvival_bounds L hD x a κ hκ t ω).2)
    ((reflectedAtomicHazard_paths_ae L hL D hD x a κ hκ).mono (fun _ hω => hω.2.2.2.1))
    T f hf (reflectedAtomicSurvivalLossStieltjes L hL D hD x a κ hκ) (fun _ => 1) hHK

theorem reflectedAtomicSurvival_product_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (f : BrownianIntegrand)
    (hf : brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure T f = f) :
    (fun ω => reflectedAtomicSurvival L D x a κ T ω * brownianIntegralGlobalPath f T ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegral brownianDyadicPath_isPreBrownianReal
        (reflectedAtomicSurvivalMultiplier L hL D hD x a κ hκ f) ω -
        ∫ r in Ioc (0 : ℝ) T.val, brownianIntegralGlobalPath f r.toNNReal ω *
          reflectedAtomicSurvival L D x a κ r.toNNReal ω
          ∂reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  have hz : brownianIntegralGlobalPath f 0 =ᵐ[brownianDyadicMeasure] (fun _ => 0) := by
    have he := brownianIntegralGlobalPath_integral_ae f 0
    rw [brownianIntegralUpTo_zero] at he
    exact he.trans (Lp.coeFn_zero ℝ 2 brownianDyadicMeasure)
  filter_upwards [reflectedAtomicSurvival_stieltjes_product_ae L hL D hD x a κ hκ T f hf,
    hall, hz] with ω he hω hzero
  rw [hzero, mul_zero, sub_zero] at he
  rw [reflectedAtomicSurvivalLoss_weighted_integral L hL D hD x a κ hκ hω
    (fun t => brownianIntegralGlobalPath f t ω) (brownianIntegralGlobalPath_continuous f ω) T] at he
  exact he

theorem reflectedAtomicSurvival_product_integrable_ae
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (f : BrownianIntegrand) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      IntegrableOn (fun r => brownianIntegralGlobalPath f r.toNNReal ω *
        reflectedAtomicSurvival L D x a κ r.toNNReal ω) (Ioc (0 : ℝ) T.val)
        (reflectedAtomicHazardTimeMeasure L hL D hD x a κ hκ ω) := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L (a i) ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L (a i))
  filter_upwards [hall] with ω hω
  exact (reflectedAtomicSurvivalLoss_weighted_integrable L hL D hD x a κ hκ hω
    (fun t => brownianIntegralGlobalPath f t ω) (brownianIntegralGlobalPath_continuous f ω) T).2

end TimeTraps.Probability

end
