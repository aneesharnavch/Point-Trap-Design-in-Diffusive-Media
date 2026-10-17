module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! The exact Lebesgue change of variables for a positively scaled and
translated occupation density. Scalar L1 weights stay L1 under the affine
map, and the inverse scale factor cancels its Lebesgue Jacobian. -/

namespace TimeTraps.Analysis

open MeasureTheory

theorem affine_comp_integrable {g : ℝ → ℝ} (hg : Integrable g volume)
    (x : ℝ) {σ : ℝ} (hσ : σ ≠ 0) : Integrable (fun b => g (x + σ * b)) volume :=
  (hg.comp_add_left x).comp_mul_left' hσ

theorem affine_density_pairing (g L : ℝ → ℝ) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ a, g a * (σ⁻¹ * L ((a - x) / σ))) = ∫ b, g (x + σ * b) * L b := by
  let H := fun b => g (x + σ * b) * L b
  have he : (fun a => g a * (σ⁻¹ * L ((a - x) / σ))) =
      (fun a => σ⁻¹ * H ((a - x) / σ)) := by
    funext a
    dsimp only [H]
    rw [show x + σ * ((a - x) / σ) = a by field_simp; ring]
    ring
  rw [he, integral_const_mul]
  have ht : (∫ a, H ((a - x) / σ)) = ∫ a, H (a / σ) :=
    integral_sub_right_eq_self (fun a => H (a / σ)) x
  rw [ht, Measure.integral_comp_div, abs_of_pos hσ, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]

theorem affine_density_integrable (g L : ℝ → ℝ) (x : ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (hH : Integrable (fun b => g (x + σ * b) * L b) volume) :
    Integrable (fun a => g a * (σ⁻¹ * L ((a - x) / σ))) volume := by
  have hi := ((hH.comp_div hσ).comp_sub_right x).const_mul σ⁻¹
  convert hi using 1
  funext a
  rw [show x + σ * ((a - x) / σ) = a by field_simp; ring]
  ring

end TimeTraps.Analysis
