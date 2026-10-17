module

public import TimeTraps.Probability.BrownianFoldSlopeBrownian
public import TimeTraps.Probability.ReflectedFoldSkorokhod

@[expose] public section

/-! The independently defined triangular fold is an actual reflected
Brownian solution: its driving integral has the full Brownian law and
its actual lattice regulators satisfy the all-time equation and boundary
support conditions. The deterministic uniqueness theorem applies to this
same constructed input. No stochastic equation is a supplied hypothesis. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem affineBrownian_reflected_construction (L : ℝ) (hL : 0 < L)
    (x : ℝ) (hx : x ∈ Icc 0 L) {σ : ℝ} (hσ : 0 < σ) :
    IsBrownianReal (brownianFoldSlopeGlobalPath L hL x hσ) brownianDyadicMeasure ∧
      ∀ᵐ ω ∂brownianDyadicMeasure,
        ReflectedFoldRegulatorPaths x σ L hσ hL ω ∧
          ∀ t : ℝ≥0, reflectedFold L (affineBrownianInput x σ t ω) = x +
            σ * brownianFoldSlopeGlobalPath L hL x hσ t ω +
              affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω := by
  refine ⟨brownianFoldSlopeGlobalPath_isBrownianReal L hL x hσ, ?_⟩
  exact (reflectedFoldRegulatorPaths_ae x hσ hL).and
    (affineBrownianFoldTanaka_global_initial_ae L hL x hx hσ)

theorem foldedTrajectory_reflectedBrownian (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (hx : x ∈ Icc 0 L) :
    ∃ W : ℝ≥0 → (ℕ → ℝ) → ℝ,
      IsBrownianReal W brownianDyadicMeasure ∧
        Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => W p.1 p.2) ∧
          ∀ᵐ ω ∂brownianDyadicMeasure,
            ReflectedFoldRegulatorPaths x (Real.sqrt (2 * D)) L
              (Real.sqrt_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hD)) hL ω ∧
            ∀ t : ℝ≥0, foldedTrajectory L D x brownianDyadicPath t ω = x +
              Real.sqrt (2 * D) * W t ω +
                affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
                  affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hD)
  refine ⟨brownianFoldSlopeGlobalPath L hL x hσ,
    brownianFoldSlopeGlobalPath_isBrownianReal L hL x hσ,
    brownianFoldSlopeGlobalPath_jointlyMeasurable L hL x hσ, ?_⟩
  exact (reflectedFoldRegulatorPaths_ae x hσ hL).and (foldedTrajectory_tanaka_ae L hL D hD x hx)

end TimeTraps.Probability
