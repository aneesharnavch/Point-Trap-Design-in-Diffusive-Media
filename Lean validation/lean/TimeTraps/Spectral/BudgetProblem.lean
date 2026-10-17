module

public import TimeTraps.Spectral.ArctanConcavity
public import TimeTraps.Spectral.PlacementUniqueness

@[expose] public section

/-! Fixed total strength, with strengths and ordered sites independently admissible. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

structure BudgetProblem (n : ℕ) where
  count_pos : 0 < n
  length : ℝ
  length_pos : 0 < length
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  budget : ℝ
  budget_pos : 0 < budget

variable {n : ℕ}

theorem BudgetProblem.count_real_pos (B : BudgetProblem n) : (0 : ℝ) < n :=
  Nat.cast_pos.mpr B.count_pos

def BudgetProblem.AdmissibleStrength (B : BudgetProblem n) (κ : Fin n → ℝ) : Prop :=
  (∀ i, 0 < κ i) ∧ (∑ i, κ i) = B.budget

def BudgetProblem.placement (B : BudgetProblem n) (κ : Fin n → ℝ)
    (hκ : B.AdmissibleStrength κ) : PlacementProblem n where
  count_pos := B.count_pos
  length := B.length
  length_pos := B.length_pos
  diffusivity := B.diffusivity
  diffusivity_pos := B.diffusivity_pos
  strength := κ
  strength_pos := hκ.1

noncomputable def BudgetProblem.uniformStrength (B : BudgetProblem n) : Fin n → ℝ :=
  fun _ => B.budget / n

theorem BudgetProblem.uniformStrength_admissible (B : BudgetProblem n) :
    B.AdmissibleStrength B.uniformStrength := by
  constructor
  · intro i
    exact div_pos B.budget_pos B.count_real_pos
  · simp only [uniformStrength, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_div_cancel₀ _ (ne_of_gt B.count_real_pos)

noncomputable def BudgetProblem.uniform (B : BudgetProblem n) : PlacementProblem n :=
  B.placement B.uniformStrength B.uniformStrength_admissible

theorem BudgetProblem.capacity_le_uniform (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ) {k : ℝ} (hk : 0 < k) :
    (∑ i, Real.arctan (κ i / (2 * B.diffusivity * k))) ≤
      ∑ i, Real.arctan (B.uniformStrength i / (2 * B.diffusivity * k)) := by
  have h := scaledArctan_sum_le B.count_pos (c := 2 * B.diffusivity * k)
    (mul_pos (mul_pos (by norm_num) B.diffusivity_pos) hk) κ hκ.1
  simpa [scaledArctan, hκ.2, uniformStrength] using h

theorem BudgetProblem.capacity_eq_iff (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ) {k : ℝ} (hk : 0 < k) :
    (∑ i, Real.arctan (κ i / (2 * B.diffusivity * k))) =
      (∑ i, Real.arctan (B.uniformStrength i / (2 * B.diffusivity * k))) ↔
        κ = B.uniformStrength := by
  have h := scaledArctan_sum_eq_iff B.count_pos (c := 2 * B.diffusivity * k)
    (mul_pos (mul_pos (by norm_num) B.diffusivity_pos) hk) κ hκ.1
  simpa [scaledArctan, hκ.2, uniformStrength, funext_iff] using h

theorem BudgetProblem.root_le_uniform (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ) :
    (B.placement κ hκ).root ≤ B.uniform.root := by
  let C := B.placement κ hκ
  apply le_capacity_root Finset.univ ⟨⟨0, B.count_pos⟩, Finset.mem_univ _⟩
    (fun i => B.uniformStrength i / (2 * B.diffusivity))
    (fun i _ => div_pos (B.uniformStrength_admissible.1 i)
      (mul_pos (by norm_num) B.diffusivity_pos))
    B.length_pos C.root_pos B.uniform.root_pos
  · simp only [phaseCapacity, div_div, ← Finset.mul_sum]
    exact B.uniform.root_equation
  · have he := C.root_equation
    have hc := B.capacity_le_uniform κ hκ C.root_pos
    change B.length * C.root = 2 * ∑ i, Real.arctan (κ i / (2 * B.diffusivity * C.root)) at he
    simp only [phaseCapacity, div_div, ← Finset.mul_sum]
    linarith

theorem BudgetProblem.root_eq_iff (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ) :
    (B.placement κ hκ).root = B.uniform.root ↔ κ = B.uniformStrength := by
  constructor
  · intro hr
    apply (B.capacity_eq_iff κ hκ B.uniform.root_pos).mp
    have he := (B.placement κ hκ).root_equation
    rw [hr] at he
    have hu := B.uniform.root_equation
    change B.length * B.uniform.root =
      2 * ∑ i, Real.arctan (κ i / (2 * B.diffusivity * B.uniform.root)) at he
    change B.length * B.uniform.root =
      2 * ∑ i, Real.arctan (B.uniformStrength i / (2 * B.diffusivity * B.uniform.root)) at hu
    linarith
  · intro h
    subst κ
    rfl

end TimeTraps.Spectral
