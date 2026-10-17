module

public import TimeTraps.Analysis.RegularSturmSpectrumEnumeration

@[expose] public section

/-! The first spectral value bounds the form on the entire selected-zero H1 space.
The proof tests positivity of the shifted form on u minus a scalar multiple
of its shifted solution, using a spectral upper bound for the compact inverse.
No operator-domain condition is imposed on the selected-zero H1 competitor. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.shifted_eigenvalue_le_first (P : RegularSturmProblem ι l r)
    (i : CompactSpectralIndex P.shiftedInverse) : i.1 ≤ (P.spectralEnumeration 0).1 := by
  have h := P.spectralEnumeration_monotone (Nat.zero_le (P.spectralEnumeration.symm i))
  simp only [Equiv.apply_symm_apply] at h
  have hi : (P.spectralEnumeration 0).1⁻¹ ≤ i.1⁻¹ := by linarith
  exact (inv_le_inv₀ (P.shiftedCompactPositiveInverse.eigenbasis_positive _)
    (P.shiftedCompactPositiveInverse.eigenbasis_positive i)).mp hi

theorem RegularSturmProblem.shiftedInverse_quadratic_le_first (P : RegularSturmProblem ι l r)
    (f : IntervalSobolevL2 l r) :
    inner ℝ f (P.shiftedInverse f) ≤ (P.spectralEnumeration 0).1 * ‖f‖ ^ 2 := by
  apply hasSum_le _ (P.shiftedCompactPositiveInverse.hasSum_quadratic f)
    ((P.eigenbasis_parseval f).mul_left (P.spectralEnumeration 0).1)
  intro i
  exact mul_le_mul_of_nonneg_right (P.shifted_eigenvalue_le_first i) (sq_nonneg _)

theorem RegularSturmProblem.shiftedForm_first_lower (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) :
    (P.spectralEnumeration 0).1⁻¹ * ‖(P.stateL u)‖ ^ 2 ≤ P.shiftedForm u u := by
  let μ := (P.spectralEnumeration 0).1
  let α := μ⁻¹
  let v := P.shiftedSolution (P.stateL u)
  have hμ : 0 < μ := P.shiftedCompactPositiveInverse.eigenbasis_positive _
  have hcross : P.shiftedForm v u = ‖(P.stateL u)‖ ^ 2 := by
    change P.shiftedForm (P.shiftedSolution (P.stateL u)) u = _
    rw [P.shiftedSolution_spec, real_inner_self_eq_norm_sq]
  have hcross' : P.shiftedForm u v = ‖(P.stateL u)‖ ^ 2 :=
    (P.shiftedForm_symmetric u v).trans hcross
  have hb : P.shiftedForm v v ≤ μ * ‖(P.stateL u)‖ ^ 2 := by
    change P.shiftedForm (P.shiftedSolution (P.stateL u)) (P.shiftedSolution (P.stateL u)) ≤ _
    rw [P.shiftedSolution_spec, ← P.shiftedInverse_apply]
    exact P.shiftedInverse_quadratic_le_first (P.stateL u)
  have hcancel : α ^ 2 * μ = α := by
    dsimp only [α]
    rw [pow_two, mul_assoc, inv_mul_cancel₀ hμ.ne', mul_one]
  have hb' : α ^ 2 * P.shiftedForm v v ≤ α * ‖(P.stateL u)‖ ^ 2 := by
    calc
      _ ≤ α ^ 2 * (μ * ‖(P.stateL u)‖ ^ 2) := mul_le_mul_of_nonneg_left hb (sq_nonneg α)
      _ = _ := by rw [← mul_assoc, hcancel]
  have hw : 0 ≤ P.shiftedForm (u - α • v) (u - α • v) := by
    obtain ⟨c, hc, hbound⟩ := P.shiftedForm_coercive
    exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans (hbound _)
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at hw
  rw [hcross, hcross'] at hw
  change α * ‖(P.stateL u)‖ ^ 2 ≤ P.shiftedForm u u
  nlinarith

theorem RegularSturmProblem.form_first_lower (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) :
    ((P.spectralEnumeration 0).1⁻¹ - P.massShift) * ‖(P.stateL u)‖ ^ 2 ≤ P.form u u := by
  have h := P.shiftedForm_first_lower u
  rw [P.shiftedForm_eq, real_inner_self_eq_norm_sq] at h
  nlinarith

end TimeTraps.Analysis
