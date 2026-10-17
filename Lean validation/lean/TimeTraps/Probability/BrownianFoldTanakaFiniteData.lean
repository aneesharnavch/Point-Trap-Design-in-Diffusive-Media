module

public import TimeTraps.Analysis.ReflectedFoldTanakaData
public import TimeTraps.Probability.BrownianAffineLocalTimeTanaka

@[expose] public section

/-! The actual stochastic and correction terms in the finite paired
absolute-value formula. Each affine sign term retains its physical sigma
factor; each correction is counted once at its lattice centre. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def affineBrownianFoldSignApprox (L x σ : ℝ) (N : ℕ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  affineBrownianSignTerm x σ 0 t ω + ∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) *
    (affineBrownianSignTerm x σ ((j + 1 : ℕ) * L) t ω +
      affineBrownianSignTerm x σ (-((j + 1 : ℕ) * L)) t ω)

def affineBrownianFoldCorrectionApprox (L x σ : ℝ) (N : ℕ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  affineBrownianTanakaCorrection x σ 0 t ω + ∑ j ∈ Finset.range N, (-1 : ℝ) ^ (j + 1) *
    (affineBrownianTanakaCorrection x σ ((j + 1 : ℕ) * L) t ω +
      affineBrownianTanakaCorrection x σ (-((j + 1 : ℕ) * L)) t ω)

theorem affineBrownianFoldSignApprox_succ (L x σ : ℝ) (N : ℕ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianFoldSignApprox L x σ (N + 1) t ω = affineBrownianFoldSignApprox L x σ N t ω +
      (-1 : ℝ) ^ (N + 1) * (affineBrownianSignTerm x σ ((N + 1 : ℕ) * L) t ω +
        affineBrownianSignTerm x σ (-((N + 1 : ℕ) * L)) t ω) := by
  simp only [affineBrownianFoldSignApprox, Finset.sum_range_succ]
  ring

theorem affineBrownianFoldCorrectionApprox_succ (L x σ : ℝ) (N : ℕ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    affineBrownianFoldCorrectionApprox L x σ (N + 1) t ω =
      affineBrownianFoldCorrectionApprox L x σ N t ω + (-1 : ℝ) ^ (N + 1) *
        (affineBrownianTanakaCorrection x σ ((N + 1 : ℕ) * L) t ω +
          affineBrownianTanakaCorrection x σ (-((N + 1 : ℕ) * L)) t ω) := by
  simp only [affineBrownianFoldCorrectionApprox, Finset.sum_range_succ]
  ring

end TimeTraps.Probability

end
