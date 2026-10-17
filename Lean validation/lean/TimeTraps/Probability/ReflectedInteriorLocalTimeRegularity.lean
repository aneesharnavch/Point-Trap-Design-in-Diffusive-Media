module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeData

@[expose] public section

/-! The two shifted lattice events give path regularity of the actual
interior correction. The full-measure event is chosen for each fixed level;
no intersection over uncountably many levels is asserted. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

def reflectedInteriorLocalTimeRegular (x σ L a : ℝ) (ω : ℕ → ℝ) : Prop :=
  affineBrownianLatticeRegular (x - a) σ L ω ∧ affineBrownianLatticeRegular (x + a) σ L ω

theorem reflectedInteriorLocalTimeRegular_measurableSet (x σ L a : ℝ) :
    MeasurableSet {ω | reflectedInteriorLocalTimeRegular x σ L a ω} :=
  (affineBrownianLatticeRegular_measurableSet (x - a) σ L).inter
    (affineBrownianLatticeRegular_measurableSet (x + a) σ L)

theorem reflectedInteriorLocalTimeRegular_ae (x σ L a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, reflectedInteriorLocalTimeRegular x σ L a ω :=
  (affineBrownianLatticeRegular_ae (x - a) σ L).and
    (affineBrownianLatticeRegular_ae (x + a) σ L)

theorem reflectedInteriorCorrection_nonneg (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (L a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ reflectedInteriorCorrection x σ L a t ω :=
  add_nonneg (affineBrownianRegulator_nonneg (x - a) hσ L 0 t ω)
    (affineBrownianRegulator_nonneg (x + a) hσ L 0 t ω)

theorem reflectedInteriorCorrection_zero {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hω : reflectedInteriorLocalTimeRegular x σ L a ω) :
    reflectedInteriorCorrection x σ L a 0 ω = 0 := by
  change affineBrownianRegulator (x - a) σ L 0 0 ω +
    affineBrownianRegulator (x + a) σ L 0 0 ω = 0
  rw [affineBrownianRegulator_zero hσ hω.1 0,
    affineBrownianRegulator_zero hσ hω.2 0, add_zero]

theorem reflectedInteriorCorrection_continuous {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω) :
    Continuous (fun t => reflectedInteriorCorrection x σ L a t ω) :=
  (affineBrownianRegulator_continuous hσ hL hω.1 0).add
    (affineBrownianRegulator_continuous hσ hL hω.2 0)

theorem reflectedInteriorCorrection_monotone {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω) :
    Monotone (fun t => reflectedInteriorCorrection x σ L a t ω) :=
  (affineBrownianRegulator_monotone hσ hL hω.1 0).add
    (affineBrownianRegulator_monotone hσ hL hω.2 0)

theorem reflectedInteriorCorrection_paths_ae (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Continuous (fun t => reflectedInteriorCorrection x σ L a t ω) ∧
      Monotone (fun t => reflectedInteriorCorrection x σ L a t ω) ∧
      reflectedInteriorCorrection x σ L a 0 ω = 0 ∧
      ∀ t, 0 ≤ reflectedInteriorCorrection x σ L a t ω := by
  filter_upwards [reflectedInteriorLocalTimeRegular_ae x σ L a] with ω hω
  exact ⟨reflectedInteriorCorrection_continuous hσ hL hω,
    reflectedInteriorCorrection_monotone hσ hL hω,
    reflectedInteriorCorrection_zero hσ hω,
    fun t => reflectedInteriorCorrection_nonneg x hσ L a t ω⟩

theorem reflectedInteriorOccupationCoefficient_nonneg (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (L a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ reflectedInteriorOccupationCoefficient x σ L a t ω :=
  div_nonneg (reflectedInteriorCorrection_nonneg x hσ L a t ω) (sq_nonneg σ)

end TimeTraps.Probability
