module

public import TimeTraps.Spectral.BudgetAsymptoticLimits
public import TimeTraps.Spectral.ArrayBudget

@[expose] public section

/-! The same asymptotic value is the attained optimum in both intrinsic cyclic
gap coordinates and arbitrary sorted physical arrays on the circle. -/

namespace TimeTraps.Spectral

open Set

theorem BudgetProblem.spectralBudgetValue_circle_maximum {n : ℕ} (B : BudgetProblem n) :
    IsGreatest B.circlePrincipalValues (spectralBudgetValue n B.diffusivity B.length B.budget) := by
  rw [B.spectralBudgetValue_eq]
  exact B.circle_joint_maximum

theorem BudgetProblem.spectralBudgetValue_array_maximum {n : ℕ} (B : BudgetProblem n) :
    IsGreatest B.arrayPrincipalValues (spectralBudgetValue n B.diffusivity B.length B.budget) := by
  rw [B.spectralBudgetValue_eq]
  exact B.array_joint_maximum

end TimeTraps.Spectral
