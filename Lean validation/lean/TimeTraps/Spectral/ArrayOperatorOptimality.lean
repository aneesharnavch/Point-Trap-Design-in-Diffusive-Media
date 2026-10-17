module

public import TimeTraps.Spectral.ArrayOperatorGround
public import TimeTraps.Spectral.ArrayExner

@[expose] public section

/-! The prescribed-strength, joint-budget and Exner placement theorems for
the actual first sorted periodic operator eigenvalue. The original physical
admissibility and complete translated equality classes are unchanged. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem PlacementProblem.array_operator_upper_bound (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.AdmissibleArray x) :
    ((C.array x hx).periodicPointProblem.spectralEnumeration 0).1⁻¹ ≤
      C.diffusivity * C.root ^ 2 := by
  rw [(C.array x hx).operator_first_eigenvalue]
  exact C.arbitrary_array_upper_bound x hx

theorem PlacementProblem.array_operator_eq_iff_sites (C : PlacementProblem n)
    (x : Fin n → ℝ) (hx : C.AdmissibleArray x) :
    ((C.array x hx).periodicPointProblem.spectralEnumeration 0).1⁻¹ =
      C.diffusivity * C.root ^ 2 ↔
      ∀ i, x i = (C.array x hx).offset + C.optimalCircle.site i := by
  rw [(C.array x hx).operator_first_eigenvalue]
  exact C.array_value_eq_iff_sites x hx

def PlacementProblem.arrayOperatorFirstValues (C : PlacementProblem n) : Set ℝ :=
  {ev | ∃ x : Fin n → ℝ, ∃ hx : C.AdmissibleArray x,
    ev = ((C.array x hx).periodicPointProblem.spectralEnumeration 0).1⁻¹}

theorem PlacementProblem.arrayOperatorFirstValues_eq (C : PlacementProblem n) :
    C.arrayOperatorFirstValues = C.arrayPrincipalValues := by
  ext ev
  simp only [arrayOperatorFirstValues, arrayPrincipalValues, mem_ofPred_eq,
    PeriodicArray.operator_first_eigenvalue]

theorem PlacementProblem.array_operator_maximum (C : PlacementProblem n) :
    IsGreatest C.arrayOperatorFirstValues (C.diffusivity * C.root ^ 2) := by
  rw [C.arrayOperatorFirstValues_eq]
  exact C.array_placement_maximum

theorem BudgetProblem.array_operator_upper_bound (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleArray x) :
    (((B.placement κ hκ).array x hx).periodicPointProblem.spectralEnumeration 0).1⁻¹ ≤
      B.diffusivity * B.uniform.root ^ 2 := by
  rw [((B.placement κ hκ).array x hx).operator_first_eigenvalue]
  exact B.arbitrary_array_upper_bound κ hκ x hx

theorem BudgetProblem.array_operator_eq_iff_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleArray x) :
    (((B.placement κ hκ).array x hx).periodicPointProblem.spectralEnumeration 0).1⁻¹ =
      B.diffusivity * B.uniform.root ^ 2 ↔
      (∀ i, κ i = B.budget / n) ∧
      ∀ i, x i = ((B.placement κ hκ).array x hx).offset + i.val * B.length / n := by
  rw [((B.placement κ hκ).array x hx).operator_first_eigenvalue]
  exact B.array_value_eq_iff_parameters κ hκ x hx

def BudgetProblem.arrayOperatorFirstValues (B : BudgetProblem n) : Set ℝ :=
  {ev | ∃ κ : Fin n → ℝ, ∃ hκ : B.AdmissibleStrength κ,
    ∃ x : Fin n → ℝ, ∃ hx : (B.placement κ hκ).AdmissibleArray x,
    ev = (((B.placement κ hκ).array x hx).periodicPointProblem.spectralEnumeration 0).1⁻¹}

theorem BudgetProblem.arrayOperatorFirstValues_eq (B : BudgetProblem n) :
    B.arrayOperatorFirstValues = B.arrayPrincipalValues := by
  ext ev
  simp only [arrayOperatorFirstValues, arrayPrincipalValues, mem_ofPred_eq,
    PeriodicArray.operator_first_eigenvalue]

theorem BudgetProblem.array_operator_maximum (B : BudgetProblem n) :
    IsGreatest B.arrayOperatorFirstValues (B.diffusivity * B.uniform.root ^ 2) := by
  rw [B.arrayOperatorFirstValues_eq]
  exact B.array_joint_maximum

theorem ExnerProblem.array_operator_upper_bound (E : ExnerProblem n)
    (x : Fin n → ℝ) (hx : E.prescribed.AdmissibleArray x) :
    ((E.prescribed.array x hx).periodicPointProblem.spectralEnumeration 0).1⁻¹ ≤
      E.wavenumber ^ 2 := by
  rw [(E.prescribed.array x hx).operator_first_eigenvalue]
  exact E.arbitrary_array_upper_bound x hx

theorem ExnerProblem.array_operator_eq_iff_regular (E : ExnerProblem n)
    (x : Fin n → ℝ) (hx : E.prescribed.AdmissibleArray x) :
    ((E.prescribed.array x hx).periodicPointProblem.spectralEnumeration 0).1⁻¹ =
      E.wavenumber ^ 2 ↔
      ∀ i, x i = (E.prescribed.array x hx).offset + i.val * (2 * Real.pi) / n := by
  rw [(E.prescribed.array x hx).operator_first_eigenvalue]
  exact E.array_value_eq_iff_regular x hx

theorem ExnerProblem.array_operator_maximum (E : ExnerProblem n) :
    IsGreatest E.prescribed.arrayOperatorFirstValues (E.wavenumber ^ 2) := by
  rw [E.prescribed.arrayOperatorFirstValues_eq]
  exact E.array_maximum

end TimeTraps.Spectral
