module

public import TimeTraps.Analysis.ItoTaylorRemainder
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-! Exact affine chain rules and derivative bounds for the physical
diffusion change of variables. The bounds are inherited from the given
smooth function; no boundedness of the function or its slope is assumed. -/

namespace TimeTraps.Analysis

open scoped NNReal

noncomputable def affineItoBase (F : ℝ → ℝ) (x σ z : ℝ) : ℝ := F (x + σ * z)

theorem affineItoBase_contDiff {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) (x σ : ℝ) :
    ContDiff ℝ 3 (affineItoBase F x σ) :=
  hF.comp (contDiff_const.add (contDiff_const.mul contDiff_id))

theorem affineItoBase_deriv {F : ℝ → ℝ} (hF : Differentiable ℝ F) (x σ : ℝ) :
    deriv (affineItoBase F x σ) = fun z => σ * deriv F (x + σ * z) := by
  funext z
  change deriv (fun y => F (x + σ * y)) z = _
  simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
    ((hF (x + σ * z)).hasDerivAt.comp z
      (((hasDerivAt_id z).const_mul σ).const_add x)).deriv

theorem affineItoBase_deriv_two {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) (x σ : ℝ) :
    deriv (deriv (affineItoBase F x σ)) = fun z => σ ^ 2 * deriv (deriv F) (x + σ * z) := by
  have h₁ : ContDiff ℝ 2 (deriv F) := hF.deriv'
  rw [affineItoBase_deriv (hF.differentiable (by norm_num)) x σ]
  change deriv (fun z => σ * affineItoBase (deriv F) x σ z) = _
  rw [deriv_const_mul_field', affineItoBase_deriv (h₁.differentiable (by norm_num)) x σ]
  funext z
  ring

theorem affineItoBase_deriv_three {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) (x σ : ℝ) :
    iteratedDeriv 3 (affineItoBase F x σ) = fun z => σ ^ 3 * iteratedDeriv 3 F (x + σ * z) := by
  have h₁ : ContDiff ℝ 2 (deriv F) := hF.deriv'
  have h₂ : ContDiff ℝ 1 (deriv (deriv F)) := h₁.deriv'
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [affineItoBase_deriv_two hF x σ]
  change deriv (fun z => σ ^ 2 * affineItoBase (deriv (deriv F)) x σ z) = _
  rw [deriv_const_mul_field', affineItoBase_deriv (h₂.differentiable (by norm_num)) x σ]
  funext z
  ring

theorem affineItoBase_bound_two {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {M : ℝ≥0} (hM : ∀ y, |deriv (deriv F) y| ≤ M.val) (x σ : ℝ) :
    ∀ z, |deriv (deriv (affineItoBase F x σ)) z| ≤
      (⟨σ ^ 2 * M.val, mul_nonneg (sq_nonneg σ) M.property⟩ : ℝ≥0).val := by
  intro z
  rw [affineItoBase_deriv_two hF x σ, abs_mul, abs_of_nonneg (sq_nonneg σ)]
  exact mul_le_mul_of_nonneg_left (hM (x + σ * z)) (sq_nonneg σ)

theorem affineItoBase_bound_three {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {M : ℝ≥0} (hM : ∀ y, |iteratedDeriv 3 F y| ≤ M.val) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ z, |iteratedDeriv 3 (affineItoBase F x σ) z| ≤
      (⟨σ ^ 3 * M.val, mul_nonneg (pow_nonneg hσ.le 3) M.property⟩ : ℝ≥0).val := by
  intro z
  rw [affineItoBase_deriv_three hF x σ, abs_mul, abs_of_nonneg (pow_nonneg hσ.le 3)]
  exact mul_le_mul_of_nonneg_left (hM (x + σ * z)) (pow_nonneg hσ.le 3)

end TimeTraps.Analysis
