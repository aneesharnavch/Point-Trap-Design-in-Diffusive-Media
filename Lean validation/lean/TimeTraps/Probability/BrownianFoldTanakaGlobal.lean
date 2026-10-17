module

public import TimeTraps.Probability.BrownianFoldTanakaLimit
public import TimeTraps.Probability.BrownianFoldSlopeGlobal
public import TimeTraps.Probability.ReflectedFoldTrajectory

@[expose] public section

/-! The actual folded affine Brownian trajectory satisfies the Tanaka
decomposition simultaneously at every time. Fixed-time integral identities
are extended from a countable dense set using continuity of all terms.
The driving term is the constructed continuous stochastic integral; its
Brownian law is a separate assertion, not a hypothesis of this result. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal ENNReal Topology

theorem affineBrownianFoldTanaka_global_fixed_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      reflectedFold L (affineBrownianInput x σ t ω) = reflectedFold L x +
        σ * brownianFoldSlopeGlobalPath L hL x hσ t ω +
          affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω := by
  filter_upwards [affineBrownianFoldTanaka_integral_ae L hL x hσ t,
    brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t] with ω he hn
  rw [hn]
  exact he

theorem affineBrownianFoldTanaka_global_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      reflectedFold L (affineBrownianInput x σ t ω) = reflectedFold L x +
        σ * brownianFoldSlopeGlobalPath L hL x hσ t ω +
          affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω := by
  have hd : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ k : ℕ,
      reflectedFold L (affineBrownianInput x σ (denseSeq ℝ≥0 k) ω) = reflectedFold L x +
        σ * brownianFoldSlopeGlobalPath L hL x hσ (denseSeq ℝ≥0 k) ω +
          affineBrownianLowerRegulator x σ L (denseSeq ℝ≥0 k) ω -
            affineBrownianUpperRegulator x σ L (denseSeq ℝ≥0 k) ω :=
    ae_all_iff.mpr (fun k => affineBrownianFoldTanaka_global_fixed_ae L hL x hσ (denseSeq ℝ≥0 k))
  filter_upwards [hd, affineBrownianLatticeRegular_ae x σ L] with ω he hr
  have hb : BrownianDyadicRegular ω := (hr 0).2.1
  have hleft : Continuous (fun t => reflectedFold L (affineBrownianInput x σ t ω)) :=
    (reflectedFold_continuous L).comp (affineBrownianInput_continuous x σ hb)
  have hright : Continuous (fun t => reflectedFold L x +
      σ * brownianFoldSlopeGlobalPath L hL x hσ t ω +
        affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω) :=
    ((continuous_const.add (continuous_const.mul (brownianFoldSlopeGlobalPath_continuous L hL x hσ ω))).add
      (affineBrownianRegulator_continuous hσ hL hr 0)).sub
        (affineBrownianRegulator_continuous hσ hL hr 1)
  have hall := (denseRange_denseSeq ℝ≥0).equalizer hleft hright (funext he)
  exact fun t => congrFun hall t

theorem affineBrownianFoldTanaka_global_initial_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) (hx : x ∈ Icc 0 L) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      reflectedFold L (affineBrownianInput x σ t ω) = x +
        σ * brownianFoldSlopeGlobalPath L hL x hσ t ω +
          affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω := by
  simpa only [reflectedFold_eq_self L hL x hx] using affineBrownianFoldTanaka_global_ae L hL x hσ

theorem foldedTrajectory_tanaka_ae (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (hx : x ∈ Icc 0 L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      foldedTrajectory L D x brownianDyadicPath t ω = x +
        Real.sqrt (2 * D) * brownianFoldSlopeGlobalPath L hL x (σ := Real.sqrt (2 * D))
          (Real.sqrt_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hD)) t ω +
        affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
          affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω :=
    affineBrownianFoldTanaka_global_initial_ae L hL x hx
      (Real.sqrt_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hD))

end TimeTraps.Probability
