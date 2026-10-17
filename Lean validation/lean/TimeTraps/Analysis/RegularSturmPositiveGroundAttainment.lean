module

public import TimeTraps.Analysis.RegularSturmPositiveGroundPhysical
public import TimeTraps.Analysis.RegularSturmPositiveGroundAbsolute

@[expose] public section

/-! The independently attained regular variable-coefficient Sturm Rayleigh minimum
has an actual physical weak eigenstate strictly positive in the open
interval. Its selected endpoint traces remain zero. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.positive_principal_eigenstate
    (P : RegularSturmProblem ι l r) :
    ∃ u : ℝ → ℝ, ∃ hu : IntervalEnergy u l r,
      ∃ huz : ∀ x ∈ P.boundary.zero_sites, u x = 0,
      (∀ x ∈ Ioo l r, 0 < u x) ∧ 0 < P.squareMass u ∧
      (∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v =
          P.principalValue * ∫ x in l..r, P.speed x * u x * v x) ∧
      (P.stateL (P.boundary.ofEnergy hu huz),
        P.principalValue • P.stateL (P.boundary.ofEnergy hu huz)) ∈ P.operator.graph := by
  obtain ⟨u, hu, huz, hn, hm, he, hg⟩ := P.nonnegative_principal_eigenstate
  have hne : ∃ x ∈ Icc l r, u x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : P.squareMass u = 0 := by
      calc
        P.squareMass u = ∫ _x in l..r, (0 : ℝ) ^ 2 := by
          apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
          intro x hx
          change P.speed x * u x ^ 2 = (0 : ℝ) ^ 2
          simp only [h x (Ioo_subset_Icc_self hx), zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
        _ = 0 := by simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), intervalIntegral.integral_zero]
    exact hm.ne' hz
  exact ⟨u, hu, huz, P.nonnegative_physical_eigenstate_pos hu huz P.principalValue hne
    (fun x _ => hn x) he, hm, he, hg⟩

end TimeTraps.Analysis
