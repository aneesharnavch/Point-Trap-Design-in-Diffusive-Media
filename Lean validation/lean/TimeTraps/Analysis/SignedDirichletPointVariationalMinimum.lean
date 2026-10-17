module

public import TimeTraps.Analysis.SignedDirichletPointVariationalProblem
public import TimeTraps.Analysis.SignedDirichletPointVariationalBound

@[expose] public section

/-! The independent full selected-zero H1 Rayleigh infimum is attained
by the first actual H1 eigenstate and equals the first original spectral
value. No positivity of that value or of the real contact strengths is
required. Empty, repeated and endpoint contacts remain allowed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedDirichletPointProblem.physical_first_lower (P : SignedDirichletPointProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    ((P.spectralEnumeration 0).1⁻¹ - P.massShift) * P.squareMass u ≤ P.quadraticForm u := by
  have h := P.form_first_lower (P.boundary.ofEnergy hu huz)
  rwa [P.squareMass_ofEnergy, P.quadraticForm_ofEnergy] at h

theorem SignedDirichletPointProblem.eigenvalue_mem_rayleigh (P : SignedDirichletPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) : i.1⁻¹ - P.massShift ∈ P.rayleighValues := by
  let v := P.eigenstate i
  have hm : 0 < P.squareMass (v.val.representative P.boundary.interval_pos) := by
    rw [P.squareMass_representative, P.eigenstate_state, P.eigenbasis.orthonormal.norm_eq_one i]
    norm_num
  have he : P.quadraticForm (v.val.representative P.boundary.interval_pos) =
      (i.1⁻¹ - P.massShift) * P.squareMass (v.val.representative P.boundary.interval_pos) := by
    rw [P.quadraticForm_representative, P.eigenstate_weak,
      real_inner_self_eq_norm_sq, P.squareMass_representative]
  refine ⟨v.val.representative P.boundary.interval_pos, (v.val.representative_spec P.boundary.interval_pos).1,
    (fun _ hx => P.boundary.representative_zero v hx), hm, ?_⟩
  rw [he, mul_div_cancel_right₀ _ hm.ne']

theorem SignedDirichletPointProblem.rayleigh_minimum (P : SignedDirichletPointProblem ι l r) :
    IsLeast P.rayleighValues P.principalValue := by
  have hmin : IsLeast P.rayleighValues ((P.spectralEnumeration 0).1⁻¹ - P.massShift) := by
    refine ⟨P.eigenvalue_mem_rayleigh (P.spectralEnumeration 0), ?_⟩
    rintro q ⟨u, hu, huz, hm, rfl⟩
    exact (le_div_iff₀ hm).mpr (P.physical_first_lower hu huz)
  have he : P.principalValue = (P.spectralEnumeration 0).1⁻¹ - P.massShift := hmin.csInf_eq
  rw [he]
  exact hmin

theorem SignedDirichletPointProblem.principalValue_eq_first (P : SignedDirichletPointProblem ι l r) :
    P.principalValue = (P.spectralEnumeration 0).1⁻¹ - P.massShift := by
  apply le_antisymm (P.rayleigh_minimum.2 (P.eigenvalue_mem_rayleigh (P.spectralEnumeration 0)))
  obtain ⟨u, hu, huz, hm, he⟩ := P.rayleigh_minimum.1
  rw [he]
  exact (le_div_iff₀ hm).mpr (P.physical_first_lower hu huz)

end TimeTraps.Analysis
