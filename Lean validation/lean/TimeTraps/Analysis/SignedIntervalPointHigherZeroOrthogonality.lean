module

public import TimeTraps.Analysis.SignedIntervalPointEigenEquivalence

@[expose] public section

/-! Orthogonality of distinct real physical weak eigenvalues is derived
from the symmetric full H1 point form. Strengths may have either sign,
and contact labels may be empty, repeated, or located at endpoints. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem intervalPointForm_symmetric (D : ℝ) (κ z : ι → ℝ)
    (l r : ℝ) (u v : ℝ → ℝ) :
    intervalPointForm D κ z l r u v = intervalPointForm D κ z l r v u := by
  unfold intervalPointForm
  congr 1
  · congr 1
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem SignedIntervalPointProblem.weak_eigen_orthogonal
    (P : SignedIntervalPointProblem ι l r) {u v : ℝ → ℝ} {ev ew : ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (heu : ∀ φ : ℝ → ℝ, IntervalEnergy φ l r →
      intervalPointForm P.diffusivity P.strength P.site l r u φ =
        ev * ∫ x in l..r, u x * φ x)
    (hev : ∀ φ : ℝ → ℝ, IntervalEnergy φ l r →
      intervalPointForm P.diffusivity P.strength P.site l r v φ =
        ew * ∫ x in l..r, v x * φ x)
    (hne : ev ≠ ew) : (∫ x in l..r, u x * v x) = 0 := by
  have h₁ := heu v hv
  have h₂ := hev u hu
  rw [intervalPointForm_symmetric P.diffusivity P.strength P.site l r v u] at h₂
  have hi : (∫ x in l..r, v x * u x) = ∫ x in l..r, u x * v x := by
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  rw [hi] at h₂
  have hm : (ev - ew) * (∫ x in l..r, u x * v x) = 0 := by
    nlinarith [h₁, h₂]
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne)

end TimeTraps.Analysis
