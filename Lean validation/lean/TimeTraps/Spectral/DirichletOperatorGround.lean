module

public import TimeTraps.Spectral.DirichletOperatorBridge
public import TimeTraps.Analysis.IntervalDirichletEnumeration

@[expose] public section

/-! The original independent Rayleigh principal value is the first sorted
eigenvalue of the actual empty-contact absorbing operator, for either
mixed orientation and for two absorbing endpoints. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis IntervalSobolevSpace

theorem DirichletInterval.principal_operator_exists (P : DirichletInterval) :
    ∃ u : IntervalDirichletSpace P.operatorBoundary, P.operatorBoundary.stateL u ≠ 0 ∧
      (P.operatorBoundary.stateL u, P.principalValue • P.operatorBoundary.stateL u) ∈
        P.dirichletPointProblem.operator.graph ∧
      EqOn (u.val.representative P.length_pos) P.groundState (Icc (0 : ℝ) P.length) := by
  let u := P.operatorOfAdmissible P.groundState_admissible
  have hp := P.operatorOfAdmissible_representative P.groundState_admissible
  have hm : 0 < P.squareMass (u.val.representative P.length_pos) := by
    have he : P.squareMass (u.val.representative P.length_pos) = P.squareMass P.groundState := by
      unfold squareMass
      apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
      intro x hx
      change u.val.representative P.length_pos x ^ 2 = P.groundState x ^ 2
      rw [hp (Ioo_subset_Icc_self hx)]
    rw [he]
    exact P.groundState_mass_pos
  refine ⟨u, ?_, ?_, hp⟩
  · intro hz
    rw [P.operator_squareMass, hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hm
    exact (lt_irrefl 0) hm
  · apply (P.dirichletPointProblem.operator_eigen_iff_physical u P.principalValue).mpr
    intro v hv hvz
    have hz : ∀ i : Empty, P.dirichletPointProblem.site i ∈ Icc (0 : ℝ) P.length :=
      fun i => nomatch i
    rw [intervalPointForm_congr P.dirichletPointProblem.diffusivity
      P.dirichletPointProblem.strength P.dirichletPointProblem.site P.length_pos.le hz
      hp (fun _ _ => rfl), P.operator_form_empty]
    have he := P.principal_ground_state.weak_form v
      ⟨hv, (P.operator_zeroTraces_iff v).mp hvz⟩
    calc
      _ = P.principalValue * ∫ x in (0 : ℝ)..P.length,
          P.groundState x * v x := he
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
        intro x hx
        change P.groundState x * v x = u.val.representative P.length_pos x * v x
        rw [hp (Ioo_subset_Icc_self hx)]

theorem DirichletInterval.principal_operator_spectral_index (P : DirichletInterval) :
    ∃ i : CompactSpectralIndex P.dirichletPointProblem.inverse, i.1⁻¹ = P.principalValue := by
  obtain ⟨u, hu, he, _⟩ := P.principal_operator_exists
  exact P.dirichletPointProblem.compactPositiveInverse.inverse_eigenvalue_index hu he

theorem DirichletInterval.principal_operator_least_spectral (P : DirichletInterval) :
    IsLeast (Set.range (fun i : CompactSpectralIndex P.dirichletPointProblem.inverse => i.1⁻¹))
      P.principalValue := by
  refine ⟨P.principal_operator_spectral_index, ?_⟩
  rintro ev ⟨i, rfl⟩
  exact P.principal_le_operator_eigenvalue i

theorem DirichletInterval.operator_first_eigenvalue (P : DirichletInterval) :
    (P.dirichletPointProblem.spectralEnumeration 0).1⁻¹ = P.principalValue := by
  apply le_antisymm _ (P.principal_le_operator_eigenvalue _)
  obtain ⟨i, hi⟩ := P.principal_operator_spectral_index
  have hm := P.dirichletPointProblem.spectralEnumeration_monotone
    (Nat.zero_le (P.dirichletPointProblem.spectralEnumeration.symm i))
  simpa only [Equiv.apply_symm_apply, hi] using hm

theorem DirichletInterval.operator_first_eigenstate_weak (P : DirichletInterval) :
    DirichletWeakEigenEquation P P.principalValue
      ((P.dirichletPointProblem.eigenstate
        (P.dirichletPointProblem.spectralEnumeration 0)).val.representative P.length_pos) := by
  have he := P.operator_eigenbasis_weak (P.dirichletPointProblem.spectralEnumeration 0)
  rwa [P.operator_first_eigenvalue] at he

theorem DirichletInterval.operator_first_eigenvalue_both (P : DirichletInterval)
    (he : P.ends = .both) :
    (P.dirichletPointProblem.spectralEnumeration 0).1⁻¹ =
      P.diffusivity * Real.pi ^ 2 / P.length ^ 2 := by
  rw [P.operator_first_eigenvalue, P.principalValue_both he]

theorem DirichletInterval.operator_first_eigenvalue_left (P : DirichletInterval)
    (he : P.ends = .left) :
    (P.dirichletPointProblem.spectralEnumeration 0).1⁻¹ =
      P.diffusivity * Real.pi ^ 2 / (4 * P.length ^ 2) := by
  rw [P.operator_first_eigenvalue, P.principalValue_left he]

theorem DirichletInterval.operator_first_eigenvalue_right (P : DirichletInterval)
    (he : P.ends = .right) :
    (P.dirichletPointProblem.spectralEnumeration 0).1⁻¹ =
      P.diffusivity * Real.pi ^ 2 / (4 * P.length ^ 2) := by
  rw [P.operator_first_eigenvalue, P.principalValue_right he]

end TimeTraps.Spectral
