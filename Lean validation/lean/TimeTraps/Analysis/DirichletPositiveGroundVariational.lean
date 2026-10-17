module

public import TimeTraps.Analysis.IntervalDirichletEnumeration
public import TimeTraps.Analysis.IntervalDirichletSpectrum
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! The first actual Dirichlet/mixed eigenvalue bounds the quadratic form
on every admissible H1 state. Equality implies the full zero-trace weak
eigen-equation, with no operator-domain assumption on the competitor. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def DirichletPointProblem.firstEigenvalue (P : DirichletPointProblem ι l r) : ℝ :=
  (P.spectralEnumeration 0).1⁻¹

theorem DirichletPointProblem.inverse_eigenvalue_le_first (P : DirichletPointProblem ι l r)
    (i : CompactSpectralIndex P.inverse) : i.1 ≤ (P.spectralEnumeration 0).1 := by
  have h := P.spectralEnumeration_monotone (Nat.zero_le (P.spectralEnumeration.symm i))
  simp only [Equiv.apply_symm_apply] at h
  exact (inv_le_inv₀ (P.compactPositiveInverse.eigenbasis_positive _)
    (P.compactPositiveInverse.eigenbasis_positive i)).mp h

theorem DirichletPointProblem.inverse_quadratic_le_first (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) :
    inner ℝ f (P.inverse f) ≤ (P.spectralEnumeration 0).1 * ‖f‖ ^ 2 := by
  apply hasSum_le _ (P.compactPositiveInverse.hasSum_quadratic f)
    ((P.compactPositiveInverse.hasSum_parseval f).mul_left (P.spectralEnumeration 0).1)
  intro i
  exact mul_le_mul_of_nonneg_right (P.inverse_eigenvalue_le_first i) (sq_nonneg _)

theorem DirichletPointProblem.form_first_lower (P : DirichletPointProblem ι l r)
    (u : IntervalDirichletSpace P.boundary) :
    P.firstEigenvalue * ‖P.boundary.stateL u‖ ^ 2 ≤ P.form u u := by
  let μ := (P.spectralEnumeration 0).1
  let α := μ⁻¹
  let v := P.solution (P.boundary.stateL u)
  have hμ : 0 < μ := P.compactPositiveInverse.eigenbasis_positive _
  have hcross : P.form v u = ‖P.boundary.stateL u‖ ^ 2 := by
    change P.form (P.solution (P.boundary.stateL u)) u = _
    rw [P.solution_spec, real_inner_self_eq_norm_sq]
  have hcross' : P.form u v = ‖P.boundary.stateL u‖ ^ 2 :=
    (P.form_symmetric u v).trans hcross
  have hb : P.form v v ≤ μ * ‖P.boundary.stateL u‖ ^ 2 := by
    change P.form (P.solution (P.boundary.stateL u)) (P.solution (P.boundary.stateL u)) ≤ _
    rw [P.solution_spec, ← P.inverse_apply]
    exact P.inverse_quadratic_le_first _
  have hcancel : α ^ 2 * μ = α := by
    dsimp only [α]
    rw [pow_two, mul_assoc, inv_mul_cancel₀ hμ.ne', mul_one]
  have hb' : α ^ 2 * P.form v v ≤ α * ‖P.boundary.stateL u‖ ^ 2 := by
    calc
      _ ≤ α ^ 2 * (μ * ‖P.boundary.stateL u‖ ^ 2) := mul_le_mul_of_nonneg_left hb (sq_nonneg α)
      _ = _ := by rw [← mul_assoc, hcancel]
  have hw : 0 ≤ P.form (u - α • v) (u - α • v) := by
    obtain ⟨c, hc, hbound⟩ := P.form_coercive
    exact (mul_nonneg (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).trans (hbound _)
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at hw
  rw [hcross, hcross'] at hw
  change α * ‖P.boundary.stateL u‖ ^ 2 ≤ P.form u u
  nlinarith

theorem DirichletPointProblem.first_minimizer_hilbert
    (P : DirichletPointProblem ι l r) (u : IntervalDirichletSpace P.boundary)
    (he : P.form u u = P.firstEigenvalue * ‖P.boundary.stateL u‖ ^ 2) :
    ∀ v : IntervalDirichletSpace P.boundary,
      P.form u v = P.firstEigenvalue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v) := by
  intro v
  let b := P.form u v - P.firstEigenvalue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v)
  let a := P.form v v - P.firstEigenvalue * ‖P.boundary.stateL v‖ ^ 2
  have hp (t : ℝ) : 0 ≤ 2 * t * b + t ^ 2 * a := by
    have h := P.form_first_lower (u + t • v)
    rw [map_add, map_smul, ← real_inner_self_eq_norm_sq] at h
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
    rw [real_inner_comm (P.boundary.stateL u) (P.boundary.stateL v), P.form_symmetric v u, he] at h
    dsimp only [a, b]
    nlinarith
  have hmin : IsLocalMin (fun t : ℝ => 2 * t * b + t ^ 2 * a) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hp t
  have hd : HasDerivAt (fun t : ℝ => 2 * t * b + t ^ 2 * a) (2 * b) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const b).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const a) using 1
    norm_num
  have hz := hmin.hasDerivAt_eq_zero hd
  dsimp only [b] at hz
  linarith

end TimeTraps.Analysis
