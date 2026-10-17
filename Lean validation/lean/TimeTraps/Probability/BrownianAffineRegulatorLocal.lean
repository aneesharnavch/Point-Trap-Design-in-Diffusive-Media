module

public import TimeTraps.Probability.BrownianAffineRegulator
public import TimeTraps.Probability.ReflectedFold

@[expose] public section

/-! Every lattice point in one regulator sum has the same deterministic
folded image. Uniform finite support therefore transfers local constancy
of the individual Tanaka corrections to the actual regulator sum. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem reflectedFold_lattice_offset (L : ℝ) (b k : ℤ) :
    reflectedFold L (((2 * k + b : ℤ) : ℝ) * L) = reflectedFold L ((b : ℝ) * L) := by
  have he : ((2 * k + b : ℤ) : ℝ) * L = (b : ℝ) * L + (k : ℝ) * (2 * L) := by
    push_cast
    ring
  rw [he, reflectedFold_int_period]

theorem affineBrownianRegulator_locally_constant {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω)
    (b : ℤ) (t : ℝ≥0)
    (ht : reflectedFold L (affineBrownianInput x σ t ω) ≠ reflectedFold L ((b : ℝ) * L)) :
    ∀ᶠ s in 𝓝 t, affineBrownianRegulator x σ L b s ω = affineBrownianRegulator x σ L b t ω := by
  obtain ⟨K, _, hK⟩ := affineBrownianRegulator_finite_horizon hσ hL hω b (t + 1)
  have he : ∀ᶠ s in 𝓝 t, ∀ k ∈ K,
      affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) s ω =
        affineBrownianTanakaCorrection x σ (((2 * k + b : ℤ) : ℝ) * L) t ω := by
    apply (eventually_all_finset K).mpr
    intro k _
    have hne : affineBrownianInput x σ t ω ≠ ((2 * k + b : ℤ) : ℝ) * L := by
      intro h
      apply ht
      rw [h, reflectedFold_lattice_offset]
    exact (affineBrownianLocalTimeRegular_locally_constant hσ (hω (2 * k + b)) t hne).mono
      (fun _ hs => hs.2)
  filter_upwards [he, Iic_mem_nhds (show t < t + 1 from lt_add_one t)] with s hs hst
  rw [hK s ⟨zero_le, hst⟩, hK t ⟨zero_le, (lt_add_one t).le⟩]
  exact Finset.sum_congr rfl hs

end TimeTraps.Probability
