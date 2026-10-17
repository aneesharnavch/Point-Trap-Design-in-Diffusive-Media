module

public import TimeTraps.Analysis.SignedIntervalPointVariationalProblem
public import TimeTraps.Analysis.SignedIntervalPointVariationalBound

@[expose] public section

/-! The independently defined full-H1 Rayleigh infimum is attained by the
first actual H1 eigenstate and equals the first unshifted spectral value.
All real contact strengths and the empty family remain permitted. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.physical_first_lower (P : SignedIntervalPointProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    ((P.spectralEnumeration 0).1⁻¹ - P.massShift) * P.squareMass u ≤ P.quadraticForm u := by
  have h := P.form_first_lower (ofEnergy hu P.interval_pos)
  rwa [P.squareMass_ofEnergy, P.quadraticForm_ofEnergy] at h

theorem SignedIntervalPointProblem.eigenvalue_mem_rayleigh (P : SignedIntervalPointProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) : i.1⁻¹ - P.massShift ∈ P.rayleighValues := by
  let v := P.eigenstate i
  have hm : 0 < P.squareMass (v.representative P.interval_pos) := by
    rw [P.squareMass_representative, P.eigenstate_state, P.eigenbasis.orthonormal.norm_eq_one i]
    norm_num
  have he : P.quadraticForm (v.representative P.interval_pos) =
      (i.1⁻¹ - P.massShift) * P.squareMass (v.representative P.interval_pos) := by
    rw [P.quadraticForm_representative, P.eigenstate_weak,
      real_inner_self_eq_norm_sq, P.squareMass_representative]
  refine ⟨v.representative P.interval_pos, (v.representative_spec P.interval_pos).1, hm, ?_⟩
  rw [he, mul_div_cancel_right₀ _ hm.ne']

theorem SignedIntervalPointProblem.rayleigh_minimum (P : SignedIntervalPointProblem ι l r) :
    IsLeast P.rayleighValues P.principalValue := by
  have hmin : IsLeast P.rayleighValues ((P.spectralEnumeration 0).1⁻¹ - P.massShift) := by
    refine ⟨P.eigenvalue_mem_rayleigh (P.spectralEnumeration 0), ?_⟩
    rintro q ⟨u, hu, hm, rfl⟩
    exact (le_div_iff₀ hm).mpr (P.physical_first_lower hu)
  have he : P.principalValue = (P.spectralEnumeration 0).1⁻¹ - P.massShift := hmin.csInf_eq
  rw [he]
  exact hmin

theorem SignedIntervalPointProblem.principalValue_eq_first (P : SignedIntervalPointProblem ι l r) :
    P.principalValue = (P.spectralEnumeration 0).1⁻¹ - P.massShift := by
  apply le_antisymm (P.rayleigh_minimum.2 (P.eigenvalue_mem_rayleigh (P.spectralEnumeration 0)))
  obtain ⟨u, hu, hm, he⟩ := P.rayleigh_minimum.1
  rw [he]
  exact (le_div_iff₀ hm).mpr (P.physical_first_lower hu)

end TimeTraps.Analysis
