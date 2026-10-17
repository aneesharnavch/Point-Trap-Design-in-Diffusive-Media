module

public import TimeTraps.Probability.BrownianAffineLocalTimeLattice
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

/-! Genuine lattice sums of the actual affine Tanaka corrections.
The offsets zero and one give the even and odd candidate regulators.
Their finite-horizon support is derived before continuity and monotonicity;
each lattice correction occurs once, without an endpoint multiplicity. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

def affineBrownianRegulator (x σ L : ℝ) (b : ℤ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  ∑' k : ℤ, affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) t ω

def affineBrownianLowerRegulator (x σ L : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  affineBrownianRegulator x σ L 0 t ω

def affineBrownianUpperRegulator (x σ L : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  affineBrownianRegulator x σ L 1 t ω

theorem affineBrownianRegulator_finite_horizon {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω)
    (b : ℤ) (T : ℝ≥0) :
    ∃ K : Finset ℤ,
      (∀ k ∉ K, ∀ s ∈ Icc (0 : ℝ≥0) T,
        affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) s ω = 0) ∧
      ∀ s ∈ Icc (0 : ℝ≥0) T,
        affineBrownianRegulator x σ L b s ω =
          ∑ k ∈ K, affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) s ω := by
  classical
  obtain ⟨J, hJ⟩ := affineBrownianLattice_uniform_finite_support hσ hL hω T
  have hpre : ((fun k : ℤ => 2 * k + b) ⁻¹' (J : Set ℤ)).Finite :=
    J.finite_toSet.preimage (fun i _ j _ hij => by omega)
  let K := hpre.toFinset
  have hz : ∀ k ∉ K, ∀ s ∈ Icc (0 : ℝ≥0) T,
      affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) s ω = 0 := by
    intro k hk s hs
    have hj : 2 * k + b ∉ J := by
      simpa only [K, Set.Finite.mem_toFinset, mem_preimage, Finset.mem_coe] using hk
    exact (hJ _ hj s hs).1
  refine ⟨K, hz, fun s hs => ?_⟩
  exact tsum_eq_sum (fun k hk => hz k hk s hs)

theorem affineBrownianRegulator_continuous {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (b : ℤ) :
    Continuous (fun t => affineBrownianRegulator x σ L b t ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨K, _, hK⟩ := affineBrownianRegulator_finite_horizon hσ hL hω b (t + 1)
  have hc : Continuous (fun s => ∑ k ∈ K,
      affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) s ω) :=
    continuous_finsetSum K (fun k _ => (affineBrownianLocalTimeRegular_paths hσ (hω (2 * k + b))).2.1)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [Iic_mem_nhds (show t < t + 1 from lt_add_one t)] with s hs
  exact hK s ⟨zero_le, hs⟩

theorem affineBrownianRegulator_monotone {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (b : ℤ) :
    Monotone (fun t => affineBrownianRegulator x σ L b t ω) := by
  intro s t hst
  change affineBrownianRegulator x σ L b s ω ≤ affineBrownianRegulator x σ L b t ω
  obtain ⟨K, _, hK⟩ := affineBrownianRegulator_finite_horizon hσ hL hω b t
  rw [hK s ⟨zero_le, hst⟩, hK t ⟨zero_le, le_rfl⟩]
  exact Finset.sum_le_sum (fun k _ =>
    (affineBrownianLocalTimeRegular_paths hσ (hω (2 * k + b))).2.2.1 hst)

theorem affineBrownianRegulator_zero {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hω : affineBrownianLatticeRegular x σ L ω) (b : ℤ) :
    affineBrownianRegulator x σ L b 0 ω = 0 := by
  have hz (k : ℤ) : affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) 0 ω = 0 :=
    (affineBrownianLocalTimeRegular_paths hσ (hω (2 * k + b))).2.2.2
  simp only [affineBrownianRegulator, hz, tsum_zero]

theorem affineBrownianRegulator_nonneg (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (L : ℝ) (b : ℤ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ affineBrownianRegulator x σ L b t ω := by
  exact tsum_nonneg (fun k => mul_nonneg hσ.le (brownianLocalTimeTimeField_nonneg _ _ _))

end TimeTraps.Probability

end
