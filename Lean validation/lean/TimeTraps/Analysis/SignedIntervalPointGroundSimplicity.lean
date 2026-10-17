module

public import TimeTraps.Analysis.SignedIntervalPointGroundSimplicityPhysical
public import TimeTraps.Analysis.SignedIntervalPointGroundSimplicityOperator

@[expose] public section

/-! A proved positive physical ground state spans every physical weak
eigenstate at the independently defined principal Rayleigh value. The
statement retains the original full H1 class and arbitrary real contacts. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.positive_ground_spans
    (P : SignedIntervalPointProblem ι l r) :
    ∃ u : ℝ → ℝ, ∃ _hu : IntervalEnergy u l r,
      (∀ x ∈ Icc l r, 0 < u x) ∧ 0 < P.squareMass u ∧
      (∀ w : ℝ → ℝ, IntervalEnergy w l r →
        intervalPointForm P.diffusivity P.strength P.site l r u w =
          P.principalValue * ∫ x in l..r, u x * w x) ∧
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ w : ℝ → ℝ, IntervalEnergy w l r →
          intervalPointForm P.diffusivity P.strength P.site l r v w =
            P.principalValue * ∫ x in l..r, v x * w x) →
        EqOn v (fun x => (v l / u l) * u x) (Icc l r) := by
  obtain ⟨u, hu, hp, hm, he, _hg⟩ := P.positive_principal_eigenstate
  refine ⟨u, hu, hp, hm, he, ?_⟩
  intro v hv hev
  exact P.principal_weak_scalar hu hv (hp l ⟨le_rfl, P.interval_pos.le⟩).ne' he hev

end TimeTraps.Analysis
