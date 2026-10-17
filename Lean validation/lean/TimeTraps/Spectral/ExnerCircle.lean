module

public import TimeTraps.Spectral.CircleBudget

@[expose] public section

/-! Positive equal-strength interactions in Exner's normalization D=1, L=2π.
The conclusion is stated for arbitrary admissible cyclic gaps. The geometric
identification of arrays modulo rotations/reflections remains a separate bridge. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

structure ExnerProblem (n : ℕ) where
  count_pos : 0 < n
  strength : ℝ
  strength_pos : 0 < strength

variable {n : ℕ}

noncomputable def ExnerProblem.budgetProblem (E : ExnerProblem n) : BudgetProblem n where
  count_pos := E.count_pos
  length := 2 * Real.pi
  length_pos := mul_pos (by norm_num) Real.pi_pos
  diffusivity := 1
  diffusivity_pos := zero_lt_one
  budget := n * E.strength
  budget_pos := mul_pos (Nat.cast_pos.mpr E.count_pos) E.strength_pos

noncomputable def ExnerProblem.prescribed (E : ExnerProblem n) : PlacementProblem n :=
  E.budgetProblem.uniform

noncomputable def ExnerProblem.wavenumber (E : ExnerProblem n) : ℝ := E.prescribed.root

theorem ExnerProblem.count_real_pos (E : ExnerProblem n) : (0 : ℝ) < n :=
  Nat.cast_pos.mpr E.count_pos

theorem ExnerProblem.prescribed_strength (E : ExnerProblem n) (i : Fin n) :
    E.prescribed.strength i = E.strength := by
  change ((n : ℝ) * E.strength) / n = E.strength
  exact mul_div_cancel_left₀ _ (ne_of_gt E.count_real_pos)

theorem ExnerProblem.wavenumber_pos (E : ExnerProblem n) : 0 < E.wavenumber := E.prescribed.root_pos

theorem ExnerProblem.wavenumber_phase (E : ExnerProblem n) :
    Real.pi * E.wavenumber / n = Real.arctan (E.strength / (2 * E.wavenumber)) := by
  have h := E.prescribed.root_equation
  change (2 * Real.pi) * E.wavenumber =
    2 * ∑ i, Real.arctan (E.prescribed.strength i / (2 * 1 * E.wavenumber)) at h
  simp only [E.prescribed_strength, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  apply (div_eq_iff (ne_of_gt E.count_real_pos)).mpr
  linarith

theorem ExnerProblem.wavenumber_range (E : ExnerProblem n) :
    E.wavenumber ∈ Ioo 0 ((n : ℝ) / 2) := by
  refine ⟨E.wavenumber_pos, ?_⟩
  have h : Real.pi * E.wavenumber / n < Real.pi / 2 := by
    rw [E.wavenumber_phase]
    exact Real.arctan_lt_pi_div_two _
  have hm := (div_lt_iff₀ E.count_real_pos).mp h
  nlinarith [Real.pi_pos]

theorem ExnerProblem.wavenumber_equation (E : ExnerProblem n) :
    E.strength = 2 * E.wavenumber * Real.tan (Real.pi * E.wavenumber / n) := by
  rw [E.wavenumber_phase, Real.tan_arctan]
  rw [mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) E.wavenumber_pos))]

theorem ExnerProblem.wavenumber_eq_of_equation (E : ExnerProblem n) {k : ℝ}
    (hk : k ∈ Ioo 0 ((n : ℝ) / 2))
    (he : E.strength = 2 * k * Real.tan (Real.pi * k / n)) : k = E.wavenumber := by
  have hz : Real.pi * k / n ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have hp := div_pos (mul_pos Real.pi_pos hk.1) E.count_real_pos
      linarith [Real.pi_pos]
    · apply (div_lt_iff₀ E.count_real_pos).mpr
      have hm := mul_lt_mul_of_pos_left hk.2 Real.pi_pos
      linarith
  have ht : E.strength / (2 * k) = Real.tan (Real.pi * k / n) := by
    rw [he, mul_div_cancel_left₀ _ (ne_of_gt (mul_pos (by norm_num) hk.1))]
  apply E.prescribed.eq_root hk.1
  change (2 * Real.pi) * k = 2 * ∑ i, Real.arctan (E.prescribed.strength i / (2 * 1 * k))
  simp only [E.prescribed_strength, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ht, Real.arctan_tan hz.1 hz.2]
  field_simp [ne_of_gt E.count_real_pos]

theorem ExnerProblem.wavenumber_existsUnique (E : ExnerProblem n) :
    ∃! k : ℝ, k ∈ Ioo 0 ((n : ℝ) / 2) ∧
      E.strength = 2 * k * Real.tan (Real.pi * k / n) :=
  ⟨E.wavenumber, ⟨E.wavenumber_range, E.wavenumber_equation⟩,
    fun _ hk => E.wavenumber_eq_of_equation hk.1 hk.2⟩

theorem ExnerProblem.regular_gap (E : ExnerProblem n) (i : Fin n) :
    E.prescribed.optimalCircleGap i = 2 * Real.pi / n := E.budgetProblem.uniform_circle_gap i

theorem ExnerProblem.regular_value (E : ExnerProblem n) :
    E.prescribed.optimalCircle.network.principalValue = E.wavenumber ^ 2 := by
  have h := E.prescribed.optimalCircle_principalValue
  change E.prescribed.optimalCircle.network.principalValue = 1 * E.wavenumber ^ 2 at h
  simpa only [one_mul] using h

theorem ExnerProblem.arbitrary_upper_bound (E : ExnerProblem n)
    (g : Fin n → ℝ) (hg : E.prescribed.AdmissibleCircle g) :
    (E.prescribed.circle g hg).network.principalValue ≤ E.wavenumber ^ 2 := by
  have h := E.prescribed.arbitrary_circle_upper_bound g hg
  change (E.prescribed.circle g hg).network.principalValue ≤ 1 * E.wavenumber ^ 2 at h
  simpa only [one_mul] using h

theorem ExnerProblem.value_eq_iff_regular (E : ExnerProblem n)
    (g : Fin n → ℝ) (hg : E.prescribed.AdmissibleCircle g) :
    (E.prescribed.circle g hg).network.principalValue = E.wavenumber ^ 2 ↔
      ∀ i, g i = 2 * Real.pi / n := by
  have h := E.prescribed.circle_value_eq_iff_gaps g hg
  change (E.prescribed.circle g hg).network.principalValue = 1 * E.wavenumber ^ 2 ↔ _ at h
  simpa only [one_mul, funext_iff, E.regular_gap] using h

theorem ExnerProblem.strict_loss (E : ExnerProblem n)
    (g : Fin n → ℝ) (hg : E.prescribed.AdmissibleCircle g)
    (hne : ∃ i, g i ≠ 2 * Real.pi / n) :
    (E.prescribed.circle g hg).network.principalValue < E.wavenumber ^ 2 := by
  apply lt_of_le_of_ne (E.arbitrary_upper_bound g hg)
  intro he
  obtain ⟨i, hi⟩ := hne
  exact hi ((E.value_eq_iff_regular g hg).mp he i)

theorem ExnerProblem.maximum (E : ExnerProblem n) :
    IsGreatest E.prescribed.circlePrincipalValues (E.wavenumber ^ 2) := by
  have h := E.prescribed.circle_placement_maximum
  change IsGreatest E.prescribed.circlePrincipalValues (1 * E.wavenumber ^ 2) at h
  simpa only [one_mul] using h

end TimeTraps.Spectral
