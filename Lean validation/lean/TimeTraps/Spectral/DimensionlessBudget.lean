module

public import TimeTraps.Spectral.BudgetOptimality

@[expose] public section

/-! The manuscript's dimensionless root, sharp spectral value and full equality case. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

variable {n : ℕ}

noncomputable def BudgetProblem.zeta (B : BudgetProblem n) : ℝ :=
  B.uniform.root * B.length / (2 * n)

theorem BudgetProblem.zeta_pos (B : BudgetProblem n) : 0 < B.zeta :=
  div_pos (mul_pos B.uniform.root_pos B.length_pos) (mul_pos (by norm_num) B.count_real_pos)

theorem BudgetProblem.zeta_eq_arctan (B : BudgetProblem n) :
    B.zeta = Real.arctan ((B.budget / n) / (2 * B.diffusivity * B.uniform.root)) := by
  have he := B.uniform.root_equation
  change B.length * B.uniform.root =
    2 * ∑ _i : Fin n, Real.arctan ((B.budget / n) / (2 * B.diffusivity * B.uniform.root)) at he
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  apply (div_eq_iff (ne_of_gt (mul_pos (by norm_num) B.count_real_pos))).mpr
  linarith

theorem BudgetProblem.zeta_lt (B : BudgetProblem n) : B.zeta < Real.pi / 2 := by
  rw [B.zeta_eq_arctan]
  exact Real.arctan_lt_pi_div_two _

theorem BudgetProblem.zeta_tan (B : BudgetProblem n) :
    Real.tan B.zeta = (B.budget / n) / (2 * B.diffusivity * B.uniform.root) := by
  rw [B.zeta_eq_arctan, Real.tan_arctan]

theorem BudgetProblem.zeta_equation (B : BudgetProblem n) :
    B.zeta * Real.tan B.zeta = B.budget * B.length / (4 * B.diffusivity * (n : ℝ) ^ 2) := by
  rw [B.zeta_tan, zeta]
  field_simp [ne_of_gt B.uniform.root_pos]
  ring

theorem positive_tan_product_strictMonoOn :
    StrictMonoOn (fun z : ℝ => z * Real.tan z) (Ioo 0 (Real.pi / 2)) := by
  intro a ha b hb hab
  have htan := Real.strictMonoOn_tan
    ⟨by linarith [Real.pi_pos, ha.1], ha.2⟩
    ⟨by linarith [Real.pi_pos, hb.1], hb.2⟩ hab
  exact mul_lt_mul hab htan.le (Real.tan_pos_of_pos_of_lt_pi_div_two ha.1 ha.2) hb.1.le

theorem BudgetProblem.zeta_eq_of_equation (B : BudgetProblem n) {z : ℝ}
    (hz : z ∈ Ioo 0 (Real.pi / 2))
    (he : z * Real.tan z = B.budget * B.length / (4 * B.diffusivity * (n : ℝ) ^ 2)) : z = B.zeta :=
  positive_tan_product_strictMonoOn.injOn hz ⟨B.zeta_pos, B.zeta_lt⟩
    (he.trans B.zeta_equation.symm)

theorem BudgetProblem.zeta_existsUnique (B : BudgetProblem n) :
    ∃! z : ℝ, z ∈ Ioo 0 (Real.pi / 2) ∧
      z * Real.tan z = B.budget * B.length / (4 * B.diffusivity * (n : ℝ) ^ 2) :=
  ⟨B.zeta, ⟨⟨B.zeta_pos, B.zeta_lt⟩, B.zeta_equation⟩,
    fun _ hz => B.zeta_eq_of_equation hz.1 hz.2⟩

theorem BudgetProblem.dimensionless_value (B : BudgetProblem n) :
    B.diffusivity * B.uniform.root ^ 2 =
      4 * B.diffusivity * (n : ℝ) ^ 2 / B.length ^ 2 * B.zeta ^ 2 := by
  unfold zeta
  field_simp [ne_of_gt B.length_pos, ne_of_gt B.count_real_pos]
  ring

theorem BudgetProblem.dimensionless_upper_bound (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    ((B.placement κ hκ).physical x hx).principalValue ≤
      4 * B.diffusivity * (n : ℝ) ^ 2 / B.length ^ 2 * B.zeta ^ 2 := by
  rw [← B.dimensionless_value]
  exact B.arbitrary_upper_bound κ hκ x hx

theorem BudgetProblem.dimensionless_equality_iff (B : BudgetProblem n)
    (κ : Fin n → ℝ) (hκ : B.AdmissibleStrength κ)
    (x : Fin n → ℝ) (hx : (B.placement κ hκ).Admissible x) :
    ((B.placement κ hκ).physical x hx).principalValue =
      4 * B.diffusivity * (n : ℝ) ^ 2 / B.length ^ 2 * B.zeta ^ 2 ↔
      (∀ i, κ i = B.budget / n) ∧
      (∀ i, x i = (2 * (i.val : ℝ) + 1) * B.length / (2 * n)) := by
  rw [← B.dimensionless_value]
  exact B.value_eq_iff_parameters κ hκ x hx

theorem BudgetProblem.dimensionless_maximum (B : BudgetProblem n) :
    IsGreatest B.principalValues
      (4 * B.diffusivity * (n : ℝ) ^ 2 / B.length ^ 2 * B.zeta ^ 2) := by
  rw [← B.dimensionless_value]
  exact B.joint_maximum

end TimeTraps.Spectral
