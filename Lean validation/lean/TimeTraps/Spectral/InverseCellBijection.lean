module

public import TimeTraps.Spectral.InverseCellProblem

@[expose] public section

/-! A genuine equivalence between admissible ordered cells and positive
strength vectors with the prescribed optimized root, including exact feasibility. -/

namespace TimeTraps.Spectral

open scoped BigOperators

variable {n : ℕ}

theorem InverseCellProblem.Strengths.phase_equation {P : InverseCellProblem n}
    {κ : Fin n → ℝ} (hκ : P.Strengths κ) :
    P.length * P.wavenumber = 2 * ∑ i, Real.arctan (κ i / (2 * P.diffusivity * P.wavenumber)) := by
  have he := (P.placement κ hκ.positive).root_equation
  rw [hκ.root_eq] at he
  exact he

theorem InverseCellProblem.strengthCell_total (P : InverseCellProblem n)
    {κ : Fin n → ℝ} (hκ : P.Strengths κ) : (∑ i, P.strengthCell κ i) = P.length := by
  unfold strengthCell
  rw [← Finset.sum_div, ← Finset.mul_sum, ← hκ.phase_equation]
  exact mul_div_cancel_right₀ _ (ne_of_gt P.wavenumber_pos)

theorem InverseCellProblem.cellStrength_admissible (P : InverseCellProblem n)
    {ℓ : Fin n → ℝ} (hℓ : P.Cells ℓ) : P.Strengths (P.cellStrength ℓ) :=
  ⟨P.cellStrength_pos hℓ, P.cellStrength_root hℓ⟩

theorem InverseCellProblem.strengthCell_admissible (P : InverseCellProblem n)
    {κ : Fin n → ℝ} (hκ : P.Strengths κ) : P.Cells (P.strengthCell κ) :=
  ⟨P.strengthCell_pos hκ.positive, P.strengthCell_total hκ, P.strengthCell_phase_lt κ⟩

noncomputable def InverseCellProblem.cellStrengthEquiv (P : InverseCellProblem n) :
    {ℓ : Fin n → ℝ // P.Cells ℓ} ≃ {κ : Fin n → ℝ // P.Strengths κ} where
  toFun ℓ := ⟨P.cellStrength ℓ.val, P.cellStrength_admissible ℓ.property⟩
  invFun κ := ⟨P.strengthCell κ.val, P.strengthCell_admissible κ.property⟩
  left_inv ℓ := Subtype.ext (P.strengthCell_cellStrength ℓ.property)
  right_inv κ := Subtype.ext (P.cellStrength_strengthCell κ.val)

theorem InverseCellProblem.cells_nonempty_iff (P : InverseCellProblem n) :
    (∃ ℓ : Fin n → ℝ, P.Cells ℓ) ↔ P.wavenumber * P.length < n * Real.pi := by
  constructor
  · rintro ⟨ℓ, hℓ⟩
    have hs : (∑ i, P.wavenumber * ℓ i) < ∑ _i : Fin n, Real.pi :=
      Finset.sum_lt_sum (fun i _ => (hℓ.phase_lt i).le)
        ⟨⟨0, P.count_pos⟩, Finset.mem_univ _, hℓ.phase_lt _⟩
    rw [← Finset.mul_sum, hℓ.total] at hs
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs
  · intro h
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.count_pos
    refine ⟨fun _ => P.length / n, ⟨fun _ => div_pos P.length_pos hn, ?_, ?_⟩⟩
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_div_cancel₀ _ (ne_of_gt hn)
    · intro i
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ hn).mpr (by simpa only [mul_comm] using h)

theorem InverseCellProblem.strengths_nonempty_iff (P : InverseCellProblem n) :
    (∃ κ : Fin n → ℝ, P.Strengths κ) ↔ P.wavenumber * P.length < n * Real.pi := by
  constructor
  · rintro ⟨κ, hκ⟩
    exact P.cells_nonempty_iff.mp ⟨P.strengthCell κ, P.strengthCell_admissible hκ⟩
  · intro h
    obtain ⟨ℓ, hℓ⟩ := P.cells_nonempty_iff.mpr h
    exact ⟨P.cellStrength ℓ, P.cellStrength_admissible hℓ⟩

theorem InverseCellProblem.strengthCell_eq_iff (P : InverseCellProblem n)
    {ℓ κ : Fin n → ℝ} (hℓ : P.Cells ℓ) :
    P.strengthCell κ = ℓ ↔ κ = P.cellStrength ℓ := by
  constructor
  · intro he
    rw [← P.cellStrength_strengthCell κ, he]
  · rintro rfl
    exact P.strengthCell_cellStrength hℓ

end TimeTraps.Spectral
