module

public import TimeTraps.Analysis.SignedPeriodicPointPositiveGroundPhysical
public import TimeTraps.Analysis.SignedPeriodicPointVariationalNonnegative

@[expose] public section

/-! The independent periodic Rayleigh minimum for arbitrary real
contacts is attained by a strictly positive physical principal state. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.positive_principal_eigenstate
    (P : SignedPeriodicPointProblem ι l r) :
    ∃ u : ℝ → ℝ, ∃ hu : IntervalEnergy u l r,
      ∃ huz : u l = u r,
      (∀ x ∈ Icc l r, 0 < u x) ∧ 0 < P.squareMass u ∧
      (∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (v l = v r) →
        intervalPointForm P.diffusivity P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, u x * v x) ∧
      (P.boundary.stateL (P.boundary.ofEnergy hu huz.symm),
        P.principalValue • P.boundary.stateL (P.boundary.ofEnergy hu huz.symm)) ∈ P.operator.graph := by
  obtain ⟨u, hu, huz, hn, hm, he, hg⟩ := P.nonnegative_principal_eigenstate
  have hne : ∃ x ∈ Icc l r, u x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : P.squareMass u = 0 := by
      calc
        P.squareMass u = ∫ _x in l..r, (0 : ℝ) ^ 2 := by
          apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
          intro x hx
          change u x ^ 2 = (0 : ℝ) ^ 2
          rw [h x (Ioo_subset_Icc_self hx)]
        _ = 0 := by simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), intervalIntegral.integral_zero]
    exact hm.ne' hz
  exact ⟨u, hu, huz, P.nonnegative_physical_eigenstate_pos hu huz P.principalValue hne
    (fun x _ => hn x) he, hm, he, hg⟩

end TimeTraps.Analysis
