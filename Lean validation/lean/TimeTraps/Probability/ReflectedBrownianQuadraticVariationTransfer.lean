module

public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariationUniform
public import TimeTraps.Probability.ReflectedBrownianConstruction

@[expose] public section

/-! The actual boundary regulator paths have vanishing stopped dyadic
quadratic variation uniformly on every compact interval, on one event.
The actual all-time reflection equation transfers any uniform quadratic
variation limit of its constructed Brownian driver to the folded path. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem reflectedFoldRegulators_quadraticVariation_uniform_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      TendstoUniformlyOn (stoppedDyadicPathQV (fun t => affineBrownianLowerRegulator x σ L t ω) T)
        (fun _ => 0) atTop (Icc 0 T) ∧
      TendstoUniformlyOn (stoppedDyadicPathQV (fun t => affineBrownianUpperRegulator x σ L t ω) T)
        (fun _ => 0) atTop (Icc 0 T) ∧
      TendstoUniformlyOn (stoppedDyadicPathQV (fun t => affineBrownianLowerRegulator x σ L t ω -
        affineBrownianUpperRegulator x σ L t ω) T) (fun _ => 0) atTop (Icc 0 T) := by
  filter_upwards [reflectedFoldRegulatorPaths_ae x hσ hL] with ω hp T
  have hl := stoppedDyadicPathQV_continuous_monotone_uniform
    (fun t => affineBrownianLowerRegulator x σ L t ω) T
    hp.lower_continuous.continuousOn (hp.lower_monotone.monotoneOn (Icc 0 T))
  have hu := stoppedDyadicPathQV_continuous_monotone_uniform
    (fun t => affineBrownianUpperRegulator x σ L t ω) T
    hp.upper_continuous.continuousOn (hp.upper_monotone.monotoneOn (Icc 0 T))
  refine ⟨hl, hu, ?_⟩
  exact finiteQuadraticVariation_uniform_sub_zero (fun n => 2 ^ n)
    (fun n s i => affineBrownianLowerRegulator x σ L (min s (brownianDyadicGrid T n i)) ω)
    (fun n s i => affineBrownianUpperRegulator x σ L (min s (brownianDyadicGrid T n i)) ω)
    (Icc 0 T) hl hu

theorem affineBrownianFold_quadraticVariation_uniform_transfer_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (T : ℝ≥0) (A : ℝ≥0 → ℝ) (M : ℝ),
      TendstoUniformlyOn (stoppedDyadicPathQV (fun t => brownianFoldSlopeGlobalPath L hL x hσ t ω) T)
        A atTop (Icc 0 T) → (∀ s ∈ Icc 0 T, A s ≤ M) →
      TendstoUniformlyOn (stoppedDyadicPathQV (fun t => reflectedFold L (affineBrownianInput x σ t ω)) T)
        (fun s => σ ^ 2 * A s) atTop (Icc 0 T) := by
  filter_upwards [affineBrownianFoldTanaka_global_ae L hL x hσ,
    reflectedFoldRegulatorPaths_ae x hσ hL] with ω he hp T A M hW hA
  have ht := stoppedDyadicPathQV_affine_regulators_uniform
    (fun t => brownianFoldSlopeGlobalPath L hL x hσ t ω)
    (fun t => affineBrownianLowerRegulator x σ L t ω)
    (fun t => affineBrownianUpperRegulator x σ L t ω) T σ (reflectedFold L x) A hW M hA
    hp.lower_continuous.continuousOn (hp.lower_monotone.monotoneOn (Icc 0 T))
    hp.upper_continuous.continuousOn (hp.upper_monotone.monotoneOn (Icc 0 T))
  have hpath : (fun t => reflectedFold L (affineBrownianInput x σ t ω)) =
      (fun t => reflectedFold L x + σ * brownianFoldSlopeGlobalPath L hL x hσ t ω +
        affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω) := funext he
  rw [hpath]
  exact ht

end TimeTraps.Probability
