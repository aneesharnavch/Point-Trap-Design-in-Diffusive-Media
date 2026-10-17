module

public import TimeTraps.Analysis.L2PointwiseLimit
public import TimeTraps.Analysis.ReflectedFoldTanakaRepresentation
public import TimeTraps.Probability.BrownianFoldSignIntegral
public import TimeTraps.Probability.BrownianFoldCorrectionLimit
public import TimeTraps.Probability.BrownianFoldSlopeContinuous

@[expose] public section

/-! The finite affine Tanaka formula stabilizes pathwise. Its stochastic
term also converges in L2 to the actual fold-slope integral, so uniqueness
of almost-everywhere limits identifies that integral with the reflected
path minus the two boundary regulators. No Brownian law for the new
integral, or reflected stochastic equation, is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter Set TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem affineBrownianFoldSignApprox_eventually_eq_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, ∀ᶠ N : ℕ in atTop,
      affineBrownianFoldSignApprox L x σ N t ω =
        reflectedFold L (affineBrownianInput x σ t ω) - reflectedFold L x -
          (affineBrownianLowerRegulator x σ L t ω -
            affineBrownianUpperRegulator x σ L t ω) := by
  filter_upwards [affineBrownianFoldTanakaApprox_decomposition_ae L x hσ,
    affineBrownianLatticeRegular_ae x σ L] with ω hd hr
  intro t
  filter_upwards [reflectedFoldTanakaApprox_eventually_eq L hL (affineBrownianInput x σ t ω),
    reflectedFoldTanakaApprox_eventually_eq L hL x,
    affineBrownianFoldCorrectionApprox_eventually_eq hσ hL hr t] with N hy hx hc
  have he := hd N t
  rw [hy, hx, hc t ⟨zero_le, le_rfl⟩] at he
  linarith

theorem affineBrownianFoldSignApprox_tendsto_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      Tendsto (fun N : ℕ => affineBrownianFoldSignApprox L x σ N t ω) atTop
        (𝓝 (reflectedFold L (affineBrownianInput x σ t ω) - reflectedFold L x -
          (affineBrownianLowerRegulator x σ L t ω -
            affineBrownianUpperRegulator x σ L t ω))) := by
  filter_upwards [affineBrownianFoldSignApprox_eventually_eq_ae L hL x hσ] with ω hω
  intro t
  apply tendsto_const_nhds.congr'
  filter_upwards [hω t] with N hN
  exact hN.symm

theorem affineBrownianFoldTanaka_integral_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      reflectedFold L (affineBrownianInput x σ t ω) = reflectedFold L x +
        σ * brownianDyadicFoldSlopeIntegral L hL x hσ t ω +
          affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω := by
  have he := real_L2_eq_ae_of_pointwise_limit
    (fun N => (affineBrownianFoldSignApprox_memLp L x σ N t).toLp
      (affineBrownianFoldSignApprox L x σ N t))
    (σ • brownianDyadicFoldSlopeIntegral L hL x hσ t)
    (fun N => affineBrownianFoldSignApprox L x σ N t)
    (fun ω => reflectedFold L (affineBrownianInput x σ t ω) - reflectedFold L x -
      (affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω))
    (fun N => (affineBrownianFoldSignApprox_memLp L x σ N t).coeFn_toLp)
    (affineBrownianFoldSignApprox_L2_tendsto L hL x hσ t)
    ((affineBrownianFoldSignApprox_tendsto_ae L hL x hσ).mono (fun _ h => h t))
  filter_upwards [he, Lp.coeFn_smul σ (brownianDyadicFoldSlopeIntegral L hL x hσ t)]
    with ω hω hs
  rw [hs, Pi.smul_apply, smul_eq_mul] at hω
  linarith

end TimeTraps.Probability
