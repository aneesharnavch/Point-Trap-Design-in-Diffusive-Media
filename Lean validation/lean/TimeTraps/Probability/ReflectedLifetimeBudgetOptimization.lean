module

public import TimeTraps.Probability.ReflectedLifetimePlacementOptimization
public import TimeTraps.Spectral.BudgetOptimality

@[expose] public section

/-! The fixed-total-budget optimum of actual lifetime logarithmic decay
is attained exactly at equal strengths and equally spaced midpoint sites.
Strengths and ordered sites range over the original independent domains. -/

namespace TimeTraps.Probability

open Set TimeTraps.Spectral

variable {n : ℕ}

noncomputable def reflectedBudgetDecayValues (B : BudgetProblem n) (z : ℝ) : Set ℝ :=
  {r | ∃ κ : Fin n → ℝ, ∃ hκ : B.AdmissibleStrength κ,
    ∃ x : Fin n → ℝ, ∃ hx : (B.placement κ hκ).Admissible x,
    r = reflectedLifetimeDecayRate ((B.placement κ hκ).physical x hx) z}

theorem reflectedBudget_decay_upper_bound (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) {z : ℝ} (hz : z ∈ Icc 0 B.length) :
    reflectedLifetimeDecayRate ((B.placement κ hκ).physical x hx) z ≤ B.diffusivity * B.uniform.root ^ 2 := by
  rw [reflectedLifetimeDecayRate_eq ((B.placement κ hκ).physical x hx) hz]
  exact B.arbitrary_upper_bound κ hκ x hx

theorem reflectedBudget_decay_eq_iff_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) {z : ℝ} (hz : z ∈ Icc 0 B.length) :
    reflectedLifetimeDecayRate ((B.placement κ hκ).physical x hx) z = B.diffusivity * B.uniform.root ^ 2 ↔
      (∀ i, κ i = B.budget / n) ∧
      (∀ i, x i = (2 * (i.val : ℝ) + 1) * B.length / (2 * n)) := by
  rw [reflectedLifetimeDecayRate_eq ((B.placement κ hκ).physical x hx) hz]
  exact B.value_eq_iff_parameters κ hκ x hx

theorem reflectedBudgetDecayValues_eq (B : BudgetProblem n)
    {z : ℝ} (hz : z ∈ Icc 0 B.length) : reflectedBudgetDecayValues B z = B.principalValues := by
  ext r
  constructor
  · rintro ⟨κ, hκ, x, hx, rfl⟩
    exact ⟨κ, hκ, x, hx, reflectedLifetimeDecayRate_eq ((B.placement κ hκ).physical x hx) hz⟩
  · rintro ⟨κ, hκ, x, hx, rfl⟩
    exact ⟨κ, hκ, x, hx, (reflectedLifetimeDecayRate_eq ((B.placement κ hκ).physical x hx) hz).symm⟩

theorem reflectedBudget_decay_maximum (B : BudgetProblem n)
    {z : ℝ} (hz : z ∈ Icc 0 B.length) :
    IsGreatest (reflectedBudgetDecayValues B z) (B.diffusivity * B.uniform.root ^ 2) := by
  rw [reflectedBudgetDecayValues_eq B hz]
  exact B.joint_maximum

theorem reflectedBudget_decay_strict_loss (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) {z : ℝ} (hz : z ∈ Icc 0 B.length)
    (hne : ¬ (κ = B.uniformStrength ∧ x = B.uniform.optimalSite)) :
    reflectedLifetimeDecayRate ((B.placement κ hκ).physical x hx) z < B.diffusivity * B.uniform.root ^ 2 := by
  rw [reflectedLifetimeDecayRate_eq ((B.placement κ hκ).physical x hx) hz]
  exact B.strict_loss_of_other_parameters κ hκ x hx hne

end TimeTraps.Probability
