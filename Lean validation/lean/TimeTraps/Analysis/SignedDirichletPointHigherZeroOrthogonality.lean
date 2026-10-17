module

public import TimeTraps.Analysis.SignedDirichletPointSpectrumEquivalence
public import TimeTraps.Analysis.SignedIntervalPointHigherZeroOrthogonality

@[expose] public section

/-! Distinct real eigenvalues are orthogonal in the actual selected-zero
physical H1 class. The symmetric point form retains arbitrary real
strengths and empty, repeated or endpoint contact labels. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedDirichletPointProblem.weak_eigen_orthogonal
    (P : SignedDirichletPointProblem ι l r) {u v : ℝ → ℝ} {ev ew : ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0)
    (heu : ∀ φ : ℝ → ℝ, IntervalEnergy φ l r →
      (∀ x ∈ P.boundary.zero_sites, φ x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u φ =
        ev * ∫ x in l..r, u x * φ x)
    (hev : ∀ φ : ℝ → ℝ, IntervalEnergy φ l r →
      (∀ x ∈ P.boundary.zero_sites, φ x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r v φ =
        ew * ∫ x in l..r, v x * φ x)
    (hne : ev ≠ ew) : (∫ x in l..r, u x * v x) = 0 := by
  have h₁ := heu v hv hvz
  have h₂ := hev u hu huz
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
