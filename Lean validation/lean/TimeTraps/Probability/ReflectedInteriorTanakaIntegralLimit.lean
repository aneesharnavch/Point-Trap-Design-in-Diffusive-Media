module

public import TimeTraps.Probability.ReflectedInteriorTanakaApproximation
public import TimeTraps.Probability.ReflectedInteriorKinkIntegrand

@[expose] public section

/-! The actual finite affine-kink integrands converge in the completed
product-L² domain to the canonical original-Brownian interior-kink
integrand. The corresponding stopped stochastic integrals converge in L². -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorFiniteIntegrand_tendsto (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun N => reflectedInteriorFiniteIntegrand L a x σ N T) atTop
      (𝓝 (reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal
        brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL a ha x hσ T)) := by
  have hh : Measurable (fun b => σ * reflectedInteriorTanakaSlope L a (x + σ * b)) :=
    (reflectedInteriorKinkCoefficient_measurable L hL a x σ).const_mul σ
  have hb (b : ℝ) : |σ * reflectedInteriorTanakaSlope L a (x + σ * b)| ≤ σ := by
    rw [abs_mul, abs_of_pos hσ]
    exact (mul_le_mul_of_nonneg_left (reflectedInteriorKinkCoefficient_bound L hL a x σ b)
      hσ.le).trans_eq (mul_one σ)
  have hS := reflectedInteriorKinkIntegrand_coe brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL a ha x hσ T
  have hS' : (reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL a ha x hσ T :
      Lp ℝ 2 (volume.prod brownianDyadicMeasure)) =ᵐ[volume.prod brownianDyadicMeasure]
      brownianBoundedProcess brownianDyadicPath
        (fun b => σ * reflectedInteriorTanakaSlope L a (x + σ * b)) T := by
    filter_upwards [hS] with p hp
    rw [hp]
    unfold brownianBoundedProcess brownianSquareProcess reflectedInteriorTanakaSlope
    ring
  apply tendsto_subtype_rng.mpr
  exact brownianBoundedProcessL2_tendsto brownianDyadicPath_jointly_measurable
    (reflectedInteriorFiniteCoefficient_measurable L a x σ) hh
    (reflectedInteriorFiniteCoefficient_bound L a x hL ha hσ) hb
    (reflectedInteriorFiniteCoefficient_tendsto L a x hL ha) T
    (fun N => (reflectedInteriorFiniteIntegrand L a x σ N T : Lp ℝ 2 (volume.prod brownianDyadicMeasure)))
    _ (fun N => reflectedInteriorFiniteIntegrand_coe L a x hσ N T) hS'

theorem reflectedInteriorFiniteIntegral_tendsto (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun N => brownianStochasticIntegralUpTo T (reflectedInteriorFiniteIntegrand L a x σ N T))
      atTop (𝓝 (reflectedInteriorKinkIntegral brownianDyadicPath_isBrownianReal
        brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL a ha x hσ T)) := by
  have h := (brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal T).continuous.continuousAt.tendsto.comp
    (reflectedInteriorFiniteIntegrand_tendsto L hL a ha x hσ T)
  rw [reflectedInteriorKinkIntegral_upTo, min_self] at h
  exact h

end TimeTraps.Probability
