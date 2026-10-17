module

public import TimeTraps.Probability.BrownianFoldTanakaFiniteData

@[expose] public section

/-! Countably many actual affine Tanaka identities give the finite fold
formula simultaneously for every cutoff and every nonnegative time.
The finite algebra does not assume a reflected equation or a new integral. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem affineBrownianLatticeTanaka_ae (x L : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ j : ℤ, ∀ t : ℝ≥0,
      |affineBrownianInput x σ t ω - (j : ℝ) * L| = |x - (j : ℝ) * L| +
        affineBrownianSignTerm x σ ((j : ℝ) * L) t ω +
          affineBrownianTanakaCorrection x σ ((j : ℝ) * L) t ω :=
  ae_all_iff.mpr (fun j => affineBrownianTanaka_decomposition_ae x hσ ((j : ℝ) * L))

theorem affineBrownianFoldTanakaApprox_of_lattice (L x σ : ℝ) {ω : ℕ → ℝ}
    (hω : ∀ j : ℤ, ∀ t : ℝ≥0,
      |affineBrownianInput x σ t ω - (j : ℝ) * L| = |x - (j : ℝ) * L| +
        affineBrownianSignTerm x σ ((j : ℝ) * L) t ω +
          affineBrownianTanakaCorrection x σ ((j : ℝ) * L) t ω)
    (N : ℕ) (t : ℝ≥0) :
    reflectedFoldTanakaApprox L N (affineBrownianInput x σ t ω) = reflectedFoldTanakaApprox L N x +
      affineBrownianFoldSignApprox L x σ N t ω + affineBrownianFoldCorrectionApprox L x σ N t ω := by
  induction N with
  | zero =>
      simpa only [reflectedFoldTanakaApprox_zero, affineBrownianFoldSignApprox,
        affineBrownianFoldCorrectionApprox, Finset.range_zero, Finset.sum_empty, add_zero,
        Int.cast_zero, zero_mul, sub_zero] using hω 0 t
  | succ N ih =>
      have hp := hω (N + 1 : ℕ) t
      have hn := hω (-(N + 1 : ℕ) : ℤ) t
      simp only [Int.cast_natCast] at hp
      simp only [Int.cast_neg, Int.cast_natCast, neg_mul, sub_neg_eq_add] at hn
      rw [reflectedFoldTanakaApprox_succ L (affineBrownianInput x σ t ω) N,
        reflectedFoldTanakaApprox_succ L x N, affineBrownianFoldSignApprox_succ,
        affineBrownianFoldCorrectionApprox_succ, ih, hp, hn]
      ring

theorem affineBrownianFoldTanakaApprox_decomposition_ae (L x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ N : ℕ, ∀ t : ℝ≥0,
      reflectedFoldTanakaApprox L N (affineBrownianInput x σ t ω) = reflectedFoldTanakaApprox L N x +
        affineBrownianFoldSignApprox L x σ N t ω + affineBrownianFoldCorrectionApprox L x σ N t ω := by
  filter_upwards [affineBrownianLatticeTanaka_ae x L hσ] with ω hω
  exact affineBrownianFoldTanakaApprox_of_lattice L x σ hω

end TimeTraps.Probability
