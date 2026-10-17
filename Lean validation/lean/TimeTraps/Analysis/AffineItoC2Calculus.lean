module

public import TimeTraps.Analysis.FiniteKinkAffine

@[expose] public section

/-! Affine transport of a C² base with a bounded second derivative.
These chain rules require no third derivative; the generic first-order
and finite-kink identities are reused unchanged. -/

namespace TimeTraps.Analysis

open scoped NNReal

theorem affineItoBase_contDiff_two {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (x σ : ℝ) :
    ContDiff ℝ 2 (affineItoBase F x σ) :=
  hF.comp (contDiff_const.add (contDiff_const.mul contDiff_id))

theorem affineItoBase_deriv_two_c2 {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (x σ : ℝ) :
    deriv (deriv (affineItoBase F x σ)) = fun z => σ ^ 2 * deriv (deriv F) (x + σ * z) := by
  have h₁ : ContDiff ℝ 1 (deriv F) := hF.deriv'
  rw [affineItoBase_deriv (hF.differentiable (by norm_num)) x σ]
  change deriv (fun z => σ * affineItoBase (deriv F) x σ z) = _
  rw [deriv_const_mul_field', affineItoBase_deriv (h₁.differentiable (by norm_num)) x σ]
  funext z
  ring

theorem affineItoBase_bound_two_c2 {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    {M : ℝ≥0} (hM : ∀ y, |deriv (deriv F) y| ≤ M.val) (x σ : ℝ) :
    ∀ z, |deriv (deriv (affineItoBase F x σ)) z| ≤
      (⟨σ ^ 2 * M.val, mul_nonneg (sq_nonneg σ) M.property⟩ : ℝ≥0).val := by
  intro z
  rw [affineItoBase_deriv_two_c2 hF x σ, abs_mul, abs_of_nonneg (sq_nonneg σ)]
  exact mul_le_mul_of_nonneg_left (hM (x + σ * z)) (sq_nonneg σ)

end TimeTraps.Analysis
