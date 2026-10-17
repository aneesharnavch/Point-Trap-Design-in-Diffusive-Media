module

public import TimeTraps.Spectral.UniformGeometry

@[expose] public section

/-! Attained spectral maximum over all positive allocations and ordered interior sites. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem BudgetProblem.root_value_le (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ) :
    B.diffusivity * (B.placement κ hκ).root ^ 2 ≤ B.diffusivity * B.uniform.root ^ 2 := by
  apply mul_le_mul_of_nonneg_left _ B.diffusivity_pos.le
  nlinarith [B.root_le_uniform κ hκ, (B.placement κ hκ).root_pos, B.uniform.root_pos]

theorem BudgetProblem.arbitrary_upper_bound (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    ((B.placement κ hκ).physical x hx).principalValue ≤ B.diffusivity * B.uniform.root ^ 2 :=
  ((B.placement κ hκ).arbitrary_upper_bound x hx).trans (B.root_value_le κ hκ)

theorem BudgetProblem.value_eq_iff (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    ((B.placement κ hκ).physical x hx).principalValue = B.diffusivity * B.uniform.root ^ 2 ↔
      κ = B.uniformStrength ∧ x = B.uniform.optimalSite := by
  constructor
  · intro he
    have hu := (B.placement κ hκ).arbitrary_upper_bound x hx
    rw [he] at hu
    change B.diffusivity * B.uniform.root ^ 2 ≤ B.diffusivity * (B.placement κ hκ).root ^ 2 at hu
    have hs := (mul_le_mul_iff_right₀ B.diffusivity_pos).mp hu
    have hr : (B.placement κ hκ).root = B.uniform.root := by
      nlinarith [B.root_le_uniform κ hκ, (B.placement κ hκ).root_pos, B.uniform.root_pos]
    have hκeq := (B.root_eq_iff κ hκ).mp hr
    subst κ
    exact ⟨rfl, (B.uniform.value_eq_iff_sites x hx).mp he⟩
  · rintro ⟨rfl, rfl⟩
    exact B.uniform.optimal_principalValue

theorem BudgetProblem.value_eq_iff_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    ((B.placement κ hκ).physical x hx).principalValue = B.diffusivity * B.uniform.root ^ 2 ↔
      (∀ i, κ i = B.budget / n) ∧
      (∀ i, x i = (2 * (i.val : ℝ) + 1) * B.length / (2 * n)) := by
  rw [B.value_eq_iff κ hκ x hx]
  simp only [funext_iff, uniformStrength, B.uniform_site]

def BudgetProblem.principalValues (B : BudgetProblem n) : Set ℝ :=
  {ev | ∃ κ : Fin n → ℝ, ∃ hκ : B.AdmissibleStrength κ,
    ∃ x : Fin n → ℝ, ∃ hx : (B.placement κ hκ).Admissible x,
      ev = ((B.placement κ hκ).physical x hx).principalValue}

theorem BudgetProblem.joint_maximum (B : BudgetProblem n) :
    IsGreatest B.principalValues (B.diffusivity * B.uniform.root ^ 2) := by
  constructor
  · exact ⟨B.uniformStrength, B.uniformStrength_admissible, B.uniform.optimalSite,
      B.uniform.optimalSite_admissible, B.uniform.optimal_principalValue.symm⟩
  · rintro ev ⟨κ, hκ, x, hx, rfl⟩
    exact B.arbitrary_upper_bound κ hκ x hx

theorem BudgetProblem.strict_loss_of_other_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x)
    (hne : ¬ (κ = B.uniformStrength ∧ x = B.uniform.optimalSite)) :
    ((B.placement κ hκ).physical x hx).principalValue < B.diffusivity * B.uniform.root ^ 2 :=
  lt_of_le_of_ne (B.arbitrary_upper_bound κ hκ x hx)
    (fun he => hne ((B.value_eq_iff κ hκ x hx).mp he))

theorem BudgetProblem.optimizer_iff (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    (∀ μ : Fin n → ℝ, ∀ hμ : B.AdmissibleStrength μ,
      ∀ y : Fin n → ℝ, ∀ hy : (B.placement μ hμ).Admissible y,
      ((B.placement μ hμ).physical y hy).principalValue ≤
        ((B.placement κ hκ).physical x hx).principalValue) ↔
      κ = B.uniformStrength ∧ x = B.uniform.optimalSite := by
  constructor
  · intro h
    apply (B.value_eq_iff κ hκ x hx).mp
    apply le_antisymm (B.arbitrary_upper_bound κ hκ x hx)
    have ho := h B.uniformStrength B.uniformStrength_admissible
      B.uniform.optimalSite B.uniform.optimalSite_admissible
    change B.uniform.optimalPhysical.principalValue ≤ _ at ho
    rwa [B.uniform.optimal_principalValue] at ho
  · intro he μ hμ y hy
    rw [(B.value_eq_iff κ hκ x hx).mpr he]
    exact B.arbitrary_upper_bound μ hμ y hy

end TimeTraps.Spectral
