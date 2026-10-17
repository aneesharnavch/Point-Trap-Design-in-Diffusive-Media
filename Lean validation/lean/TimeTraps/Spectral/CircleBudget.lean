module

public import TimeTraps.Spectral.BudgetOptimality
public import TimeTraps.Spectral.CircleOptimality

@[expose] public section

/-! Attained spectral maximum over all positive allocations and positive cyclic gaps. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem BudgetProblem.uniform_circle_gap (B : BudgetProblem n) (i : Fin n) :
    B.uniform.optimalCircleGap i = B.length / n := by
  rw [B.uniform.optimalCircleGap_cells, B.uniform_cellLength, B.uniform_cellLength]
  ring

theorem BudgetProblem.arbitrary_circle_upper_bound (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleCircle x) :
    ((B.placement κ hκ).circle x hx).network.principalValue ≤ B.diffusivity * B.uniform.root ^ 2 :=
  ((B.placement κ hκ).arbitrary_circle_upper_bound x hx).trans (B.root_value_le κ hκ)

theorem BudgetProblem.circle_value_eq_iff (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleCircle x) :
    ((B.placement κ hκ).circle x hx).network.principalValue = B.diffusivity * B.uniform.root ^ 2 ↔
      κ = B.uniformStrength ∧ x = B.uniform.optimalCircleGap := by
  constructor
  · intro he
    have hu := (B.placement κ hκ).arbitrary_circle_upper_bound x hx
    rw [he] at hu
    change B.diffusivity * B.uniform.root ^ 2 ≤ B.diffusivity * (B.placement κ hκ).root ^ 2 at hu
    have hs := (mul_le_mul_iff_right₀ B.diffusivity_pos).mp hu
    have hr : (B.placement κ hκ).root = B.uniform.root := by
      nlinarith [B.root_le_uniform κ hκ, (B.placement κ hκ).root_pos, B.uniform.root_pos]
    have hκeq := (B.root_eq_iff κ hκ).mp hr
    subst κ
    exact ⟨rfl, (B.uniform.circle_value_eq_iff_gaps x hx).mp he⟩
  · rintro ⟨rfl, rfl⟩
    exact B.uniform.optimalCircle_principalValue

theorem BudgetProblem.circle_value_eq_iff_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleCircle x) :
    ((B.placement κ hκ).circle x hx).network.principalValue = B.diffusivity * B.uniform.root ^ 2 ↔
      (∀ i, κ i = B.budget / n) ∧
      (∀ i, x i = B.length / n) := by
  rw [B.circle_value_eq_iff κ hκ x hx]
  simp only [funext_iff, uniformStrength, B.uniform_circle_gap]

def BudgetProblem.circlePrincipalValues (B : BudgetProblem n) : Set ℝ :=
  {ev | ∃ κ : Fin n → ℝ, ∃ hκ : B.AdmissibleStrength κ,
    ∃ x : Fin n → ℝ, ∃ hx : (B.placement κ hκ).AdmissibleCircle x,
      ev = ((B.placement κ hκ).circle x hx).network.principalValue}

theorem BudgetProblem.circle_joint_maximum (B : BudgetProblem n) :
    IsGreatest B.circlePrincipalValues (B.diffusivity * B.uniform.root ^ 2) := by
  constructor
  · exact ⟨B.uniformStrength, B.uniformStrength_admissible, B.uniform.optimalCircleGap,
      B.uniform.optimalCircleGap_admissible, B.uniform.optimalCircle_principalValue.symm⟩
  · rintro ev ⟨κ, hκ, x, hx, rfl⟩
    exact B.arbitrary_circle_upper_bound κ hκ x hx

theorem BudgetProblem.circle_strict_loss_of_other_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleCircle x)
    (hne : ¬ (κ = B.uniformStrength ∧ x = B.uniform.optimalCircleGap)) :
    ((B.placement κ hκ).circle x hx).network.principalValue < B.diffusivity * B.uniform.root ^ 2 :=
  lt_of_le_of_ne (B.arbitrary_circle_upper_bound κ hκ x hx)
    (fun he => hne ((B.circle_value_eq_iff κ hκ x hx).mp he))

theorem BudgetProblem.circle_optimizer_iff (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleCircle x) :
    (∀ μ : Fin n → ℝ, ∀ hμ : B.AdmissibleStrength μ,
      ∀ y : Fin n → ℝ, ∀ hy : (B.placement μ hμ).AdmissibleCircle y,
      ((B.placement μ hμ).circle y hy).network.principalValue ≤
        ((B.placement κ hκ).circle x hx).network.principalValue) ↔
      κ = B.uniformStrength ∧ x = B.uniform.optimalCircleGap := by
  constructor
  · intro h
    apply (B.circle_value_eq_iff κ hκ x hx).mp
    apply le_antisymm (B.arbitrary_circle_upper_bound κ hκ x hx)
    have ho := h B.uniformStrength B.uniformStrength_admissible
      B.uniform.optimalCircleGap B.uniform.optimalCircleGap_admissible
    change B.uniform.optimalCircle.network.principalValue ≤ _ at ho
    rwa [B.uniform.optimalCircle_principalValue] at ho
  · intro he μ hμ y hy
    rw [(B.circle_value_eq_iff κ hκ x hx).mpr he]
    exact B.arbitrary_circle_upper_bound μ hμ y hy

end TimeTraps.Spectral
