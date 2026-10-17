module

public import TimeTraps.Analysis.IntegerAlternatingSum
public import TimeTraps.Probability.BrownianFoldTanakaFiniteData
public import TimeTraps.Probability.BrownianAffineRegulator

@[expose] public section

/-! The paired finite Tanaka corrections stabilize to the actual lower
regulator minus the upper regulator, uniformly before each finite horizon.
This follows from the derived finite lattice support and exact integer
parity algebra, with no reflected stochastic equation assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem affineBrownianFoldCorrectionApprox_eventually_eq {L x σ : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (T : ℝ≥0) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ≥0) T,
      affineBrownianFoldCorrectionApprox L x σ N t ω =
        affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω := by
  obtain ⟨J, hJ⟩ := affineBrownianLattice_uniform_finite_support hσ hL hω T
  filter_upwards [eventually_ge_atTop (J.sup Int.natAbs)] with N hN
  intro t ht
  let f : ℤ → ℝ := fun j => affineBrownianTanakaCorrection x σ ((j : ℝ) * L) t ω
  have hz : ∀ j ∉ J, f j = 0 := fun j hj => (hJ j hj t ht).1
  have hb : ∀ j ∈ J, j.natAbs ≤ N := fun j hj => (Finset.le_sup hj).trans hN
  have he := integerAlternatingSum_pair_eq_of_support f J hz N hb
  simpa only [f, affineBrownianFoldCorrectionApprox, affineBrownianLowerRegulator,
    affineBrownianUpperRegulator, affineBrownianRegulator, Int.add_zero, Int.cast_zero,
    Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast, Int.cast_one, Int.cast_ofNat,
    Nat.cast_add, Nat.cast_one, zero_mul, neg_mul] using he

theorem affineBrownianFoldCorrectionApprox_tendsto {L x σ : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (t : ℝ≥0) :
    Tendsto (fun N : ℕ => affineBrownianFoldCorrectionApprox L x σ N t ω) atTop
      (𝓝 (affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω)) := by
  have he := (affineBrownianFoldCorrectionApprox_eventually_eq hσ hL hω t).mono
    (fun _ h => h t ⟨zero_le, le_rfl⟩)
  change (fun N : ℕ => affineBrownianFoldCorrectionApprox L x σ N t ω) =ᶠ[atTop]
    (fun _ => affineBrownianLowerRegulator x σ L t ω - affineBrownianUpperRegulator x σ L t ω) at he
  exact tendsto_const_nhds.congr' he.symm

end TimeTraps.Probability
