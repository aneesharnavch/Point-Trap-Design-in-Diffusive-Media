module

public import TimeTraps.Spectral.CircleWeak
public import TimeTraps.Spectral.ExnerCircle

@[expose] public section

/-! Periodic optimization for the independent single-interval H1 Rayleigh
minimum. Sites are the ordered prefix sums of the positive cyclic gaps, with
one trap anchored at zero. Rotation of arbitrary physical arrays is separate. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem CircleProblem.periodic_principal_bound (C : CircleProblem n) :
    C.periodicPrincipalValue ≤ C.diffusivity * C.prescribed.root ^ 2 := by
  rw [C.periodicPrincipalValue_eq]
  exact C.principalValue_le_root

theorem PlacementProblem.optimalCircle_periodicValue (C : PlacementProblem n) :
    C.optimalCircle.periodicPrincipalValue = C.diffusivity * C.root ^ 2 := by
  rw [C.optimalCircle.periodicPrincipalValue_eq]
  exact C.optimalCircle_principalValue

theorem PlacementProblem.arbitrary_periodic_upper_bound (C : PlacementProblem n)
    (g : Fin n → ℝ) (hg : C.AdmissibleCircle g) :
    (C.circle g hg).periodicPrincipalValue ≤ C.diffusivity * C.root ^ 2 := by
  rw [(C.circle g hg).periodicPrincipalValue_eq]
  exact C.arbitrary_circle_upper_bound g hg

theorem PlacementProblem.periodic_value_eq_iff_gaps (C : PlacementProblem n)
    (g : Fin n → ℝ) (hg : C.AdmissibleCircle g) :
    (C.circle g hg).periodicPrincipalValue = C.diffusivity * C.root ^ 2 ↔
      g = C.optimalCircleGap := by
  rw [(C.circle g hg).periodicPrincipalValue_eq]
  exact C.circle_value_eq_iff_gaps g hg

theorem PlacementProblem.periodic_optimizer_iff (C : PlacementProblem n)
    (g : Fin n → ℝ) (hg : C.AdmissibleCircle g) :
    (∀ d : Fin n → ℝ, ∀ hd : C.AdmissibleCircle d,
      (C.circle d hd).periodicPrincipalValue ≤ (C.circle g hg).periodicPrincipalValue) ↔
      g = C.optimalCircleGap := by
  simp_rw [CircleProblem.periodicPrincipalValue_eq]
  exact C.circle_optimizer_iff g hg

def PlacementProblem.periodicPrincipalValues (C : PlacementProblem n) : Set ℝ :=
  {ev | ∃ g : Fin n → ℝ, ∃ hg : C.AdmissibleCircle g,
    ev = (C.circle g hg).periodicPrincipalValue}

theorem PlacementProblem.periodic_placement_maximum (C : PlacementProblem n) :
    IsGreatest C.periodicPrincipalValues (C.diffusivity * C.root ^ 2) := by
  have he : C.periodicPrincipalValues = C.circlePrincipalValues := by
    ext ev
    simp only [periodicPrincipalValues, circlePrincipalValues, mem_ofPred_eq,
      CircleProblem.periodicPrincipalValue_eq]
  rw [he]
  exact C.circle_placement_maximum

theorem BudgetProblem.arbitrary_periodic_upper_bound (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (g : Fin n → ℝ) (hg : (B.placement κ hκ).AdmissibleCircle g) :
    ((B.placement κ hκ).circle g hg).periodicPrincipalValue ≤ B.diffusivity * B.uniform.root ^ 2 := by
  rw [CircleProblem.periodicPrincipalValue_eq]
  exact B.arbitrary_circle_upper_bound κ hκ g hg

theorem BudgetProblem.periodic_value_eq_iff_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (g : Fin n → ℝ) (hg : (B.placement κ hκ).AdmissibleCircle g) :
    ((B.placement κ hκ).circle g hg).periodicPrincipalValue = B.diffusivity * B.uniform.root ^ 2 ↔
      (∀ i, κ i = B.budget / n) ∧ (∀ i, g i = B.length / n) := by
  rw [CircleProblem.periodicPrincipalValue_eq]
  exact B.circle_value_eq_iff_parameters κ hκ g hg

def BudgetProblem.periodicPrincipalValues (B : BudgetProblem n) : Set ℝ :=
  {ev | ∃ κ : Fin n → ℝ, ∃ hκ : B.AdmissibleStrength κ,
    ∃ g : Fin n → ℝ, ∃ hg : (B.placement κ hκ).AdmissibleCircle g,
      ev = ((B.placement κ hκ).circle g hg).periodicPrincipalValue}

theorem BudgetProblem.periodic_joint_maximum (B : BudgetProblem n) :
    IsGreatest B.periodicPrincipalValues (B.diffusivity * B.uniform.root ^ 2) := by
  have he : B.periodicPrincipalValues = B.circlePrincipalValues := by
    ext ev
    simp only [periodicPrincipalValues, circlePrincipalValues, mem_ofPred_eq,
      CircleProblem.periodicPrincipalValue_eq]
  rw [he]
  exact B.circle_joint_maximum

theorem ExnerProblem.arbitrary_periodic_upper_bound (E : ExnerProblem n)
    (g : Fin n → ℝ) (hg : E.prescribed.AdmissibleCircle g) :
    (E.prescribed.circle g hg).periodicPrincipalValue ≤ E.wavenumber ^ 2 := by
  rw [CircleProblem.periodicPrincipalValue_eq]
  exact E.arbitrary_upper_bound g hg

theorem ExnerProblem.periodic_value_eq_iff_regular (E : ExnerProblem n)
    (g : Fin n → ℝ) (hg : E.prescribed.AdmissibleCircle g) :
    (E.prescribed.circle g hg).periodicPrincipalValue = E.wavenumber ^ 2 ↔
      ∀ i, g i = 2 * Real.pi / n := by
  rw [CircleProblem.periodicPrincipalValue_eq]
  exact E.value_eq_iff_regular g hg

theorem ExnerProblem.periodic_strict_loss (E : ExnerProblem n)
    (g : Fin n → ℝ) (hg : E.prescribed.AdmissibleCircle g) (hne : ∃ i, g i ≠ 2 * Real.pi / n) :
    (E.prescribed.circle g hg).periodicPrincipalValue < E.wavenumber ^ 2 := by
  rw [CircleProblem.periodicPrincipalValue_eq]
  exact E.strict_loss g hg hne

theorem ExnerProblem.periodic_maximum (E : ExnerProblem n) :
    IsGreatest E.prescribed.periodicPrincipalValues (E.wavenumber ^ 2) := by
  have h := E.prescribed.periodic_placement_maximum
  change IsGreatest E.prescribed.periodicPrincipalValues (1 * E.wavenumber ^ 2) at h
  simpa only [one_mul] using h

end TimeTraps.Spectral
