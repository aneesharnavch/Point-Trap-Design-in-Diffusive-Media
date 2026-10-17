module

public import TimeTraps.Spectral.StrengthRootComparison

@[expose] public section

/-! Ordered inverse design at prescribed positive length, diffusivity and
wavenumber. Strength admissibility uses the actual optimized root. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

structure InverseCellProblem (n : ℕ) where
  count_pos : 0 < n
  length : ℝ
  length_pos : 0 < length
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  wavenumber : ℝ
  wavenumber_pos : 0 < wavenumber

variable {n : ℕ}

def InverseCellProblem.placement (P : InverseCellProblem n) (κ : Fin n → ℝ)
    (hκ : ∀ i, 0 < κ i) : PlacementProblem n where
  count_pos := P.count_pos
  length := P.length
  length_pos := P.length_pos
  diffusivity := P.diffusivity
  diffusivity_pos := P.diffusivity_pos
  strength := κ
  strength_pos := hκ

structure InverseCellProblem.Cells (P : InverseCellProblem n) (ℓ : Fin n → ℝ) : Prop where
  positive : ∀ i, 0 < ℓ i
  total : (∑ i, ℓ i) = P.length
  phase_lt : ∀ i, P.wavenumber * ℓ i < Real.pi

structure InverseCellProblem.Strengths (P : InverseCellProblem n) (κ : Fin n → ℝ) : Prop where
  positive : ∀ i, 0 < κ i
  root_eq : (P.placement κ positive).root = P.wavenumber

noncomputable def InverseCellProblem.cellStrength (P : InverseCellProblem n)
    (ℓ : Fin n → ℝ) (i : Fin n) : ℝ :=
  2 * P.diffusivity * P.wavenumber * Real.tan (P.wavenumber * ℓ i / 2)

noncomputable def InverseCellProblem.strengthCell (P : InverseCellProblem n)
    (κ : Fin n → ℝ) (i : Fin n) : ℝ :=
  2 * Real.arctan (κ i / (2 * P.diffusivity * P.wavenumber)) / P.wavenumber

theorem InverseCellProblem.half_phase_mem (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) (i : Fin n) :
    P.wavenumber * ℓ i / 2 ∈ Ioo 0 (Real.pi / 2) :=
  ⟨div_pos (mul_pos P.wavenumber_pos (hℓ.positive i)) (by norm_num), by linarith [hℓ.phase_lt i]⟩

theorem InverseCellProblem.cellStrength_pos (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) (i : Fin n) : 0 < P.cellStrength ℓ i :=
  mul_pos (mul_pos (mul_pos (by norm_num) P.diffusivity_pos) P.wavenumber_pos)
    (Real.tan_pos_of_pos_of_lt_pi_div_two (P.half_phase_mem hℓ i).1 (P.half_phase_mem hℓ i).2)

theorem InverseCellProblem.cellStrength_angle (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) (i : Fin n) :
    Real.arctan (P.cellStrength ℓ i / (2 * P.diffusivity * P.wavenumber)) =
      P.wavenumber * ℓ i / 2 := by
  unfold cellStrength
  rw [mul_div_cancel_left₀ _ (ne_of_gt
    (mul_pos (mul_pos (by norm_num) P.diffusivity_pos) P.wavenumber_pos))]
  exact Real.arctan_tan (by linarith [(P.half_phase_mem hℓ i).1, Real.pi_pos])
    (P.half_phase_mem hℓ i).2

theorem InverseCellProblem.strengthCell_cellStrength (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) : P.strengthCell (P.cellStrength ℓ) = ℓ := by
  funext i
  unfold strengthCell
  rw [P.cellStrength_angle hℓ i]
  field_simp [ne_of_gt P.wavenumber_pos]

theorem InverseCellProblem.cellStrength_strengthCell (P : InverseCellProblem n)
    (κ : Fin n → ℝ) : P.cellStrength (P.strengthCell κ) = κ := by
  funext i
  unfold cellStrength strengthCell
  have ht : P.wavenumber *
      (2 * Real.arctan (κ i / (2 * P.diffusivity * P.wavenumber)) / P.wavenumber) / 2 =
        Real.arctan (κ i / (2 * P.diffusivity * P.wavenumber)) := by
    field_simp [ne_of_gt P.wavenumber_pos]
  rw [ht, Real.tan_arctan]
  field_simp [ne_of_gt P.diffusivity_pos, ne_of_gt P.wavenumber_pos]

theorem InverseCellProblem.strengthCell_pos (P : InverseCellProblem n)
    {κ : Fin n → ℝ} (hκ : ∀ i, 0 < κ i) (i : Fin n) : 0 < P.strengthCell κ i :=
  div_pos (mul_pos (by norm_num) (Real.arctan_pos.mpr
    (div_pos (hκ i) (mul_pos (mul_pos (by norm_num) P.diffusivity_pos) P.wavenumber_pos))))
    P.wavenumber_pos

theorem InverseCellProblem.strengthCell_phase_lt (P : InverseCellProblem n)
    (κ : Fin n → ℝ) (i : Fin n) : P.wavenumber * P.strengthCell κ i < Real.pi := by
  have he : P.wavenumber * P.strengthCell κ i =
      2 * Real.arctan (κ i / (2 * P.diffusivity * P.wavenumber)) := by
    unfold strengthCell
    field_simp [ne_of_gt P.wavenumber_pos]
  rw [he]
  linarith [Real.arctan_lt_pi_div_two (κ i / (2 * P.diffusivity * P.wavenumber))]

theorem InverseCellProblem.cellStrength_root (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) :
    (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).root = P.wavenumber := by
  symm
  apply (P.placement (P.cellStrength ℓ) (P.cellStrength_pos hℓ)).eq_root P.wavenumber_pos
  change P.length * P.wavenumber =
    2 * ∑ i, Real.arctan (P.cellStrength ℓ i / (2 * P.diffusivity * P.wavenumber))
  simp_rw [P.cellStrength_angle hℓ]
  rw [← Finset.sum_div, ← Finset.mul_sum, hℓ.total]
  ring

end TimeTraps.Spectral
