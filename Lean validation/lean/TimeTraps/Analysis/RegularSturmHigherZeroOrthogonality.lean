module

public import TimeTraps.Analysis.RegularSturmSpectrumEquivalence
public import TimeTraps.Analysis.SignedIntervalPointHigherZeroOrthogonality

@[expose] public section

/-! Distinct real eigenvalues are orthogonal in the actual selected-zero
physical H1 class. The symmetric point form retains arbitrary real
strengths and empty, repeated or endpoint contact labels. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.weak_eigen_orthogonal
    (P : RegularSturmProblem ι l r) {u v : ℝ → ℝ} {ev ew : ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hvz : ∀ x ∈ P.boundary.zero_sites, v x = 0)
    (heu : ∀ φ : ℝ → ℝ, IntervalEnergy φ l r →
      (∀ x ∈ P.boundary.zero_sites, φ x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u φ =
        ev * ∫ x in l..r, P.speed x * u x * φ x)
    (hev : ∀ φ : ℝ → ℝ, IntervalEnergy φ l r →
      (∀ x ∈ P.boundary.zero_sites, φ x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r v φ =
        ew * ∫ x in l..r, P.speed x * v x * φ x)
    (hne : ev ≠ ew) : (∫ x in l..r, P.speed x * u x * v x) = 0 := by
  have h₁ := heu v hv hvz
  have h₂ := hev u hu huz
  have hs : regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r v u =
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u v := by
    rw [← P.form_ofEnergy hv hu hvz huz, ← P.form_ofEnergy hu hv huz hvz]
    exact P.form_symmetric _ _
  rw [hs] at h₂
  have hi : (∫ x in l..r, P.speed x * v x * u x) = ∫ x in l..r, P.speed x * u x * v x := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hi] at h₂
  have hm : (ev - ew) * (∫ x in l..r, P.speed x * u x * v x) = 0 := by
    nlinarith [h₁, h₂]
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hne)

end TimeTraps.Analysis
