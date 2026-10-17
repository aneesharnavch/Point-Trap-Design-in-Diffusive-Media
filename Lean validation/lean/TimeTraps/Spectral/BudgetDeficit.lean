module

public import TimeTraps.Spectral.SpectralDeficit
public import TimeTraps.Spectral.DimensionlessBudget

@[expose] public section

/-! Zero phase deficit characterizes the physical fixed-budget optimizer. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

variable {n : ℕ}

theorem SpectralProblem.principal_mean_phase_mem (P : SpectralProblem n) :
    P.principalWavenumber * P.length / (2 * n) ∈ Ioo 0 (Real.pi / 2) := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  exact E.mean_phase_mem P.principalWavenumber_pos P.principalWavenumber_sq

theorem SpectralProblem.principal_spectral_deficit_nonneg (P : SpectralProblem n) :
    0 ≤ P.spectralDeficit P.principalWavenumber := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  exact E.spectral_deficit_nonneg P.principalWavenumber_pos P.principalWavenumber_sq

theorem BudgetProblem.deficit_eq_zero_iff_value (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    let P := (B.placement κ hκ).physical x hx
    P.spectralDeficit P.principalWavenumber = 0 ↔
      P.principalValue = B.diffusivity * B.uniform.root ^ 2 := by
  let P := (B.placement κ hκ).physical x hx
  change P.spectralDeficit P.principalWavenumber = 0 ↔ _
  have hk := P.principalWavenumber_pos
  have hn : (0 : ℝ) < 2 * n := mul_pos (by norm_num) B.count_real_pos
  constructor
  · intro hz
    change (∑ i, κ i) / (B.diffusivity * P.principalWavenumber) -
      2 * n * Real.tan (P.principalWavenumber * B.length / (2 * n)) = 0 at hz
    rw [hκ.2] at hz
    have hK : B.budget =
        (2 * n * Real.tan (P.principalWavenumber * B.length / (2 * n))) *
          (B.diffusivity * P.principalWavenumber) :=
      (div_eq_iff (ne_of_gt (mul_pos B.diffusivity_pos hk))).mp (sub_eq_zero.mp hz)
    have he : (P.principalWavenumber * B.length / (2 * n)) *
        Real.tan (P.principalWavenumber * B.length / (2 * n)) =
          B.budget * B.length / (4 * B.diffusivity * (n : ℝ) ^ 2) := by
      rw [hK]
      field_simp [ne_of_gt B.diffusivity_pos, ne_of_gt B.count_real_pos]
      ring
    have hζ := B.zeta_eq_of_equation P.principal_mean_phase_mem he
    change P.principalWavenumber * B.length / (2 * n) =
      B.uniform.root * B.length / (2 * n) at hζ
    have hr : P.principalWavenumber = B.uniform.root := by
      have hm := (div_left_inj' (ne_of_gt hn)).mp hζ
      exact mul_right_cancel₀ (ne_of_gt B.length_pos) hm
    rw [P.principalValue_formula, hr]
    rfl
  · intro he
    have hr := P.principalWavenumber_eq_of_value B.uniform.root_pos he
    change (∑ i, κ i) / (B.diffusivity * P.principalWavenumber) -
      2 * n * Real.tan (P.principalWavenumber * B.length / (2 * n)) = 0
    rw [hκ.2, hr]
    change B.budget / (B.diffusivity * B.uniform.root) - 2 * n * Real.tan B.zeta = 0
    rw [B.zeta_tan]
    field_simp [ne_of_gt B.diffusivity_pos, ne_of_gt B.uniform.root_pos,
      ne_of_gt B.count_real_pos]
    ring

theorem BudgetProblem.deficit_eq_zero_iff_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    let P := (B.placement κ hκ).physical x hx
    P.spectralDeficit P.principalWavenumber = 0 ↔
      (∀ i, κ i = B.budget / n) ∧
      (∀ i, x i = (2 * (i.val : ℝ) + 1) * B.length / (2 * n)) :=
  (B.deficit_eq_zero_iff_value κ hκ x hx).trans (B.value_eq_iff_parameters κ hκ x hx)

theorem BudgetProblem.deficit_pos_of_other_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x)
    (hne : ¬ ((∀ i, κ i = B.budget / n) ∧
      (∀ i, x i = (2 * (i.val : ℝ) + 1) * B.length / (2 * n)))) :
    let P := (B.placement κ hκ).physical x hx
    0 < P.spectralDeficit P.principalWavenumber := by
  let P := (B.placement κ hκ).physical x hx
  exact lt_of_le_of_ne P.principal_spectral_deficit_nonneg
    (fun h => hne ((B.deficit_eq_zero_iff_parameters κ hκ x hx).mp h.symm))

theorem BudgetProblem.phase_loss_equality_iff_parameters (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x)
    (E : PositiveEigenstate ((B.placement κ hκ).physical x hx)
      ((B.placement κ hκ).physical x hx).principalValue) :
    let P := (B.placement κ hκ).physical x hx
    let k := P.principalWavenumber
    ((∀ i : Fin n, E.phase k i.succ 0 = -E.phase k i.castSucc (P.shooting.gap i.castSucc)) ∧
      (∀ i, E.phaseDelta k i = k * B.length / n)) ↔
        (∀ i, κ i = B.budget / n) ∧
        (∀ i, x i = (2 * (i.val : ℝ) + 1) * B.length / (2 * n)) := by
  let P := (B.placement κ hκ).physical x hx
  exact (E.spectral_deficit_eq_zero_iff P.principalWavenumber_pos
    P.principalWavenumber_sq).symm.trans (B.deficit_eq_zero_iff_parameters κ hκ x hx)

end TimeTraps.Spectral
