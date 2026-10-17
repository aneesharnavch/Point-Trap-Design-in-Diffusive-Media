module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeSpatialMeasurable
public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimePaths

@[expose] public section

/-! The physical continuous version agrees with the actual fixed-site
coefficient for all compact times on one event. Occupation density is rho
times this coefficient; the coefficient itself has the source's speed-mass
normalization. No uncountable equality event for the old raw field is asserted. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistanceLocalTimeSpatialVersion_fixed_level_all_times (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (a : Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : BrownianCompactTime T,
      reversibleResistanceLocalTimeSpatialVersion A x T S hS a ω t =
        reversibleResistanceLocalTime A x a.val t.val ω := by
  filter_upwards [reflectedLocalTimeSpatialVersion_fixed_level_all_times A.resistanceLength
    A.resistanceLength_pos 1 zero_lt_one (A.resistance x) S (resistanceInteriorCoordinate A a)] with ω hω
  intro t
  exact hω (reversibleResistanceCompactInverseTime A x T S hS t ω)

theorem reversibleResistanceLocalTimeSpatialVersion_density_normalization (A : IntervalMedium) (x : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (a : Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : BrownianCompactTime T,
      reversibleResistanceOccupationDensity A x t.val ω a.val = A.source.density a.val *
        reversibleResistanceLocalTimeSpatialVersion A x T S hS a ω t := by
  filter_upwards [reversibleResistanceLocalTimeSpatialVersion_fixed_level_all_times A x T S hS a,
    reversibleResistanceLocalTime_density_normalization A x a.property] with ω hω hd
  intro t
  rw [hd t.val, hω t]

theorem reversibleResistanceLocalTimeSpatialVersion_exists (A : IntervalMedium) (x : ℝ) (T : ℝ≥0) :
    ∃ V : Ioo A.source.left A.source.right → (ℕ → ℝ) → C(BrownianCompactTime T, ℝ),
      (∀ ω, Continuous (fun a => V a ω)) ∧
      Measurable (fun p : (Ioo A.source.left A.source.right × BrownianCompactTime T) × (ℕ → ℝ) =>
        V p.1.1 p.2 p.1.2) ∧
      (∀ a, ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : BrownianCompactTime T,
        V a ω t = reversibleResistanceLocalTime A x a.val t.val ω) ∧
      (∀ a, ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : BrownianCompactTime T,
        reversibleResistanceOccupationDensity A x t.val ω a.val = A.source.density a.val * V a ω t) := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  exact ⟨reversibleResistanceLocalTimeSpatialVersion A x T S hS,
    reversibleResistanceLocalTimeSpatialVersion_continuous A x T S hS,
    reversibleResistanceLocalTimeSpatialVersion_jointlyMeasurable A x T S hS,
    reversibleResistanceLocalTimeSpatialVersion_fixed_level_all_times A x T S hS,
    reversibleResistanceLocalTimeSpatialVersion_density_normalization A x T S hS⟩

end TimeTraps.Probability
