module

public import TimeTraps.Probability.ReflectedInteriorTanakaFiniteFormula
public import TimeTraps.Probability.ReflectedInteriorTanakaIntegralLimit
public import TimeTraps.Probability.ReflectedInteriorTanakaCorrectionExpansion
public import TimeTraps.Probability.BrownianItoPathwiseLimit

@[expose] public section

/-! Actual single-interior-kink Tanaka for the folded affine Brownian
trajectory. The finite affine identities, L² stochastic-integral limit,
and pathwise stabilized correction sums determine the normalization.
The stochastic integral is with respect to the original Brownian process. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorTanaka_formula (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (fun ω => |reflectedFold L (affineBrownianInput x σ T ω) - a| - |reflectedFold L x - a|)
      =ᵐ[brownianDyadicMeasure] (fun ω =>
        reflectedInteriorKinkIntegral brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
          brownianDyadicPath_jointly_measurable L hL a ha x hσ T ω +
        reflectedInteriorCorrection x σ L a T ω - affineBrownianLowerRegulator x σ L T ω -
          affineBrownianUpperRegulator x σ L T ω) := by
  let S (N : ℕ) := brownianStochasticIntegralUpTo T (reflectedInteriorFiniteIntegrand L a x σ N T)
  let H (ω : ℕ → ℝ) := |reflectedFold L (affineBrownianInput x σ T ω) - a| - |reflectedFold L x - a|
  let HN (N : ℕ) (ω : ℕ → ℝ) := reflectedInteriorTanakaApprox L a N (affineBrownianInput x σ T ω) -
    reflectedInteriorTanakaApprox L a N x
  let R (N : ℕ) (ω : ℕ → ℝ) := reflectedInteriorTanakaCorrectionSum x σ L a N T ω + (H ω - HN N ω)
  let r (ω : ℕ → ℝ) := reflectedInteriorCorrection x σ L a T ω -
    affineBrownianLowerRegulator x σ L T ω - affineBrownianUpperRegulator x σ L T ω
  have hR : ∀ᵐ ω ∂brownianDyadicMeasure, Tendsto (fun N => R N ω) atTop (𝓝 (r ω)) := by
    filter_upwards [reflectedInteriorTanakaCorrectionSum_eventually_eq_ae x hσ hL a] with ω hω
    have he : (fun N => R N ω) =ᶠ[atTop] (fun _ => r ω) := by
      filter_upwards [hω T,
        reflectedInteriorTanakaApprox_eventually_eq L a (affineBrownianInput x σ T ω) hL ⟨ha.1.le, ha.2.le⟩,
        reflectedInteriorTanakaApprox_eventually_eq L a x hL ⟨ha.1.le, ha.2.le⟩] with N hK hG hx
      dsimp only [R, H, HN, r]
      rw [hK T ⟨zero_le, le_rfl⟩, hG, hx]
      ring
    exact tendsto_const_nhds.congr' he.symm
  have hH (N : ℕ) : H =ᵐ[brownianDyadicMeasure] (fun ω => S N ω + R N ω) := by
    filter_upwards [reflectedInteriorFinite_formula L a x hσ N T] with ω hω
    rw [reflectedInteriorFinite_correction_sum] at hω
    change HN N ω = S N ω + reflectedInteriorTanakaCorrectionSum x σ L a N T ω at hω
    dsimp only [R]
    linarith
  have he := ae_eq_lp_limit_of_pathwise_remainder S
    (reflectedInteriorKinkIntegral brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable L hL a ha x hσ T) R r H
    (reflectedInteriorFiniteIntegral_tendsto L hL a ha x hσ T) hR hH
  filter_upwards [he] with ω hω
  change H ω = _
  rw [hω]
  dsimp only [r]
  ring

end TimeTraps.Probability
