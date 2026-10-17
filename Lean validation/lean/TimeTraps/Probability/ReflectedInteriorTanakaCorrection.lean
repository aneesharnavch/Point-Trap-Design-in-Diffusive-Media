module

public import TimeTraps.Probability.ReflectedInteriorTanakaFiniteSums

@[expose] public section

/-! Exact stabilization of the actual interior and boundary correction
lattice sums on each finite time horizon. Uniform finite support comes
from the actual affine path range on three fixed lattice events. -/

noncomputable section

namespace TimeTraps.Probability

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

def reflectedInteriorTanakaCorrectionSum (x σ L a : ℝ) (N : ℕ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  integerPairedPartialSum (fun k =>
    affineBrownianTanakaCorrection (x - a) σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω) N +
  integerPairedPartialSum (fun k =>
    affineBrownianTanakaCorrection (x + a) σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω) N -
  integerPairedPartialSum (fun k =>
    affineBrownianTanakaCorrection x σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω) N -
  integerSplitPartialSum (fun k =>
    affineBrownianTanakaCorrection x σ (((2 * k + 1 : ℤ) : ℝ) * L) t ω) N

theorem reflectedInteriorTanakaCorrectionSum_eventually_eq {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω)
    (ha : reflectedInteriorLocalTimeRegular x σ L a ω) (T : ℝ≥0) :
    ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ≥0) T,
      reflectedInteriorTanakaCorrectionSum x σ L a N t ω =
        reflectedInteriorCorrection x σ L a t ω - affineBrownianLowerRegulator x σ L t ω -
          affineBrownianUpperRegulator x σ L t ω := by
  obtain ⟨J0, hJ0, _⟩ := affineBrownianRegulator_finite_horizon hσ hL hω 0 T
  obtain ⟨J1, hJ1, _⟩ := affineBrownianRegulator_finite_horizon hσ hL hω 1 T
  obtain ⟨Ja, hJa, _⟩ := affineBrownianRegulator_finite_horizon hσ hL ha.1 0 T
  obtain ⟨Jb, hJb, _⟩ := affineBrownianRegulator_finite_horizon hσ hL ha.2 0 T
  have hz := integerPartialSums_eventually_eq
    (fun k t => affineBrownianTanakaCorrection x σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω)
    (Icc (0 : ℝ≥0) T) J0 hJ0
  have ho := integerPartialSums_eventually_eq
    (fun k t => affineBrownianTanakaCorrection x σ (((2 * k + 1 : ℤ) : ℝ) * L) t ω)
    (Icc (0 : ℝ≥0) T) J1 hJ1
  have hminus := integerPartialSums_eventually_eq
    (fun k t => affineBrownianTanakaCorrection (x - a) σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω)
    (Icc (0 : ℝ≥0) T) Ja hJa
  have hplus := integerPartialSums_eventually_eq
    (fun k t => affineBrownianTanakaCorrection (x + a) σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω)
    (Icc (0 : ℝ≥0) T) Jb hJb
  filter_upwards [hz, ho, hminus, hplus] with N hn0 hn1 hna hnb
  intro t ht
  unfold reflectedInteriorTanakaCorrectionSum
  rw [(hna t ht).1, (hnb t ht).1, (hn0 t ht).1, (hn1 t ht).2]
  rfl

theorem reflectedInteriorTanakaCorrectionSum_eventually_eq_ae (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ T : ℝ≥0,
      ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ≥0) T,
        reflectedInteriorTanakaCorrectionSum x σ L a N t ω =
          reflectedInteriorCorrection x σ L a t ω - affineBrownianLowerRegulator x σ L t ω -
            affineBrownianUpperRegulator x σ L t ω := by
  filter_upwards [affineBrownianLatticeRegular_ae x σ L,
    reflectedInteriorLocalTimeRegular_ae x σ L a] with ω hω ha
  exact reflectedInteriorTanakaCorrectionSum_eventually_eq hσ hL hω ha

end TimeTraps.Probability

end
