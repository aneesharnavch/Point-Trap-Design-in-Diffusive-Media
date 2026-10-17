module

public import TimeTraps.Analysis.SignedIntervalPointMinimizerPhysical
public import TimeTraps.Analysis.SignedIntervalPointNonnegative

@[expose] public section

/-! The nonnegative physical Rayleigh minimizer is now an actual nonzero
weak eigenstate and belongs to the original signed operator graph.
Strict positivity and eigenspace simplicity are separate assertions. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.nonnegative_principal_eigenstate
    (P : SignedIntervalPointProblem ι l r) :
    ∃ u : ℝ → ℝ, ∃ hu : IntervalEnergy u l r,
      (∀ x, 0 ≤ u x) ∧ 0 < P.squareMass u ∧
      (∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, u x * v x) ∧
      ((ofEnergy hu P.interval_pos).state,
        P.principalValue • (ofEnergy hu P.interval_pos).state) ∈ P.operator.graph := by
  obtain ⟨u, hu, hnonneg, hm, hmin⟩ := P.nonnegative_rayleigh_minimizer
  exact ⟨u, hu, hnonneg, hm, P.minimizer_weak hu hm hmin,
    P.minimizer_operator_graph hu hm hmin⟩

end TimeTraps.Analysis
