module

public import TimeTraps.Spectral.ArrayOptimality

@[expose] public section

/-! Fixed-budget optimization over every sorted physical array, including
arbitrary positions of the first trap. Equality gives one regular array
translated by that first position. -/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem BudgetProblem.uniform_circle_site (B : BudgetProblem n) (i : Fin n) :
    B.uniform.optimalCircle.site i = i.val * B.length / n := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero =>
      have hz : B.uniform.optimalCircle.site (0 : Fin (n + 1)) = 0 := B.uniform.optimalCircle.site_zero
      simpa using hz
    | succ j ih =>
      have h := B.uniform.optimalCircle.boundary_succ j.castSucc
      change B.uniform.optimalCircle.site j.succ = B.uniform.optimalCircle.site j.castSucc +
        B.uniform.optimalCircleGap j.castSucc at h
      rw [h, ih, B.uniform_circle_gap]
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      ring

theorem BudgetProblem.arbitrary_array_upper_bound (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleArray x) :
    ((B.placement κ hκ).array x hx).principalValue ≤ B.diffusivity * B.uniform.root ^ 2 :=
  ((B.placement κ hκ).arbitrary_array_upper_bound x hx).trans (B.root_value_le κ hκ)

theorem BudgetProblem.array_value_eq_iff (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleArray x) :
    ((B.placement κ hκ).array x hx).principalValue = B.diffusivity * B.uniform.root ^ 2 ↔
      κ = B.uniformStrength ∧
      ∀ i, x i = ((B.placement κ hκ).array x hx).offset + i.val * B.length / n := by
  constructor
  · intro he
    have hu := (B.placement κ hκ).arbitrary_array_upper_bound x hx
    rw [he] at hu
    change B.diffusivity * B.uniform.root ^ 2 ≤ B.diffusivity * (B.placement κ hκ).root ^ 2 at hu
    have hs := (mul_le_mul_iff_right₀ B.diffusivity_pos).mp hu
    have hr : (B.placement κ hκ).root = B.uniform.root := by
      nlinarith [B.root_le_uniform κ hκ, (B.placement κ hκ).root_pos, B.uniform.root_pos]
    have hκeq := (B.root_eq_iff κ hκ).mp hr
    subst κ
    refine ⟨rfl, ?_⟩
    have hxopt := (B.uniform.array_value_eq_iff_sites x hx).mp he
    simpa only [B.uniform_circle_site, PeriodicArray.offset, PeriodicArray.first,
      PlacementProblem.array] using hxopt
  · rintro ⟨rfl, hs⟩
    apply (B.uniform.array_value_eq_iff_sites x hx).mpr
    simpa only [B.uniform_circle_site, PeriodicArray.offset, PeriodicArray.first,
      PlacementProblem.array] using hs

theorem BudgetProblem.array_value_eq_iff_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleArray x) :
    ((B.placement κ hκ).array x hx).principalValue = B.diffusivity * B.uniform.root ^ 2 ↔
      (∀ i, κ i = B.budget / n) ∧
      ∀ i, x i = ((B.placement κ hκ).array x hx).offset + i.val * B.length / n := by
  rw [B.array_value_eq_iff κ hκ x hx]
  simp only [funext_iff, uniformStrength]

def BudgetProblem.arrayPrincipalValues (B : BudgetProblem n) : Set ℝ :=
  {ev | ∃ κ : Fin n → ℝ, ∃ hκ : B.AdmissibleStrength κ,
    ∃ x : Fin n → ℝ, ∃ hx : (B.placement κ hκ).AdmissibleArray x,
      ev = ((B.placement κ hκ).array x hx).principalValue}

theorem BudgetProblem.array_joint_maximum (B : BudgetProblem n) :
    IsGreatest B.arrayPrincipalValues (B.diffusivity * B.uniform.root ^ 2) := by
  constructor
  · exact ⟨B.uniformStrength, B.uniformStrength_admissible, B.uniform.optimalCircle.site,
      B.uniform.optimalCircle_sites_admissible, B.uniform.optimal_array_value.symm⟩
  · rintro ev ⟨κ, hκ, x, hx, rfl⟩
    exact B.arbitrary_array_upper_bound κ hκ x hx

theorem BudgetProblem.array_strict_loss (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).AdmissibleArray x)
    (hne : ¬ (κ = B.uniformStrength ∧
      ∀ i, x i = ((B.placement κ hκ).array x hx).offset + i.val * B.length / n)) :
    ((B.placement κ hκ).array x hx).principalValue < B.diffusivity * B.uniform.root ^ 2 :=
  lt_of_le_of_ne (B.arbitrary_array_upper_bound κ hκ x hx)
    (fun he => hne ((B.array_value_eq_iff κ hκ x hx).mp he))

end TimeTraps.Spectral
