module

public import TimeTraps.Analysis.AffineItoCalculus
public import TimeTraps.Analysis.FiniteKinkCalculus

@[expose] public section

/-! Positive affine transport carries every kink and its midpoint slope,
scaling the coefficients without changing their signs. Repeated sites are retained. -/

namespace TimeTraps.Analysis

variable {ι : Type*}

theorem affineKink_coordinate (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (a z : ℝ) :
    x + σ * z - a = σ * (z - (a - x) / σ) := by
  field_simp
  ring

theorem affineKink_sign (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (a z : ℝ) :
    Real.sign (x + σ * z - a) = Real.sign (z - (a - x) / σ) := by
  rw [affineKink_coordinate x hσ a z]
  rcases lt_trichotomy (z - (a - x) / σ) 0 with hn | hz | hp
  · rw [Real.sign_of_neg hn, Real.sign_of_neg (mul_neg_of_pos_of_neg hσ hn)]
  · rw [hz, mul_zero]
  · rw [Real.sign_of_pos hp, Real.sign_of_pos (mul_pos hσ hp)]

theorem finiteKinkPotential_affine (F : ℝ → ℝ) (s : Finset ι) (a c : ι → ℝ)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : ℝ) :
    finiteKinkPotential F s a c (x + σ * z) =
      finiteKinkPotential (affineItoBase F x σ) s
        (fun i => (a i - x) / σ) (fun i => σ * c i) z := by
  simp only [finiteKinkPotential, affineItoBase]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [affineKink_coordinate x hσ (a i) z, abs_mul, abs_of_pos hσ]
  ring

theorem finiteKinkSlope_affine {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    (s : Finset ι) (a c : ι → ℝ) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (z : ℝ) :
    finiteKinkSlope (affineItoBase F x σ) s
      (fun i => (a i - x) / σ) (fun i => σ * c i) z =
      σ * finiteKinkSlope F s a c (x + σ * z) := by
  simp only [finiteKinkSlope, affineItoBase_deriv hF x σ, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [affineKink_sign x hσ (a i) z]
  ring

end TimeTraps.Analysis
