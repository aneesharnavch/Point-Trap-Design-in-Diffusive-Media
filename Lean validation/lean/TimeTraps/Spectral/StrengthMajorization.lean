module

public import TimeTraps.Spectral.StrengthRootComparison
public import TimeTraps.Spectral.ArctanConcavity
public import TimeTraps.Analysis.MajorizationConcavity

@[expose] public section

/-! Strict Schur concavity of the actual optimally placed principal value.
Majorization retains its standard sorted-partial-sum meaning. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ}

theorem scaledArctan_sum_le_of_majorizes {x y : Fin n → ℝ} (h : Majorizes x y)
    {c : ℝ} (hc : 0 < c) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    (∑ i, scaledArctan c (x i)) ≤ ∑ i, scaledArctan c (y i) :=
  h.concave_sum_le (scaledArctan_strictConcaveOn hc).concaveOn
    (fun t _ => (scaledArctan_hasDerivAt hc t).differentiableAt) hx hy

theorem scaledArctan_sum_lt_of_majorizes {x y : Fin n → ℝ} (h : Majorizes x y)
    {c : ℝ} (hc : 0 < c) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ) :
    (∑ i, scaledArctan c (x i)) < ∑ i, scaledArctan c (y i) :=
  h.strictConcave_sum_lt (scaledArctan_strictConcaveOn hc)
    (fun t _ => (scaledArctan_hasDerivAt hc t).differentiableAt) hx hy hne

theorem scaledArctan_sum_eq_iff_of_majorizes {x y : Fin n → ℝ} (h : Majorizes x y)
    {c : ℝ} (hc : 0 < c) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    (∑ i, scaledArctan c (x i)) = ∑ i, scaledArctan c (y i) ↔
      ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ :=
  h.strictConcave_sum_eq_iff (scaledArctan_strictConcaveOn hc)
    (fun t _ => (scaledArctan_hasDerivAt hc t).differentiableAt) hx hy

theorem PlacementProblem.root_le_of_majorizes (C B : PlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (h : Majorizes C.strength B.strength) : C.root ≤ B.root := by
  apply C.root_le_of_phase_sum_le B hL
  intro k hk
  rw [hD]
  exact scaledArctan_sum_le_of_majorizes h
    (mul_pos (mul_pos (by norm_num) B.diffusivity_pos) hk) C.strength_pos B.strength_pos

theorem PlacementProblem.root_lt_of_majorizes (C B : PlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (h : Majorizes C.strength B.strength)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ) : C.root < B.root := by
  apply C.root_lt_of_phase_sum_lt B hL
  intro k hk
  rw [hD]
  exact scaledArctan_sum_lt_of_majorizes h
    (mul_pos (mul_pos (by norm_num) B.diffusivity_pos) hk) C.strength_pos B.strength_pos hne

theorem PlacementProblem.root_eq_of_strength_permutation (C B : PlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (h : ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ) : C.root = B.root := by
  have hs := (descending_eq_iff_permuted C.strength B.strength).mpr h
  apply le_antisymm (C.root_le_of_majorizes B hL hD (Majorizes.of_permuted h))
  exact B.root_le_of_majorizes C hL.symm hD.symm
    (Majorizes.of_permuted ((descending_eq_iff_permuted B.strength C.strength).mp hs.symm))

theorem PlacementProblem.root_eq_iff_of_majorizes (C B : PlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (h : Majorizes C.strength B.strength) :
    C.root = B.root ↔ ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ := by
  constructor
  · intro he
    by_contra hne
    exact (C.root_lt_of_majorizes B hL hD h hne).ne he
  · exact C.root_eq_of_strength_permutation B hL hD

theorem PlacementProblem.schur_le (C B : PlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (h : Majorizes C.strength B.strength) :
    C.optimalPhysical.principalValue ≤ B.optimalPhysical.principalValue := by
  rw [C.optimal_principalValue, B.optimal_principalValue, hD]
  have hs : C.root ^ 2 ≤ B.root ^ 2 := by
    nlinarith [C.root_le_of_majorizes B hL hD h, C.root_pos, B.root_pos]
  exact mul_le_mul_of_nonneg_left hs B.diffusivity_pos.le

theorem PlacementProblem.schur_lt (C B : PlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (h : Majorizes C.strength B.strength)
    (hne : ¬ ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ) :
    C.optimalPhysical.principalValue < B.optimalPhysical.principalValue := by
  rw [C.optimal_principalValue, B.optimal_principalValue, hD]
  have hs : C.root ^ 2 < B.root ^ 2 := by
    nlinarith [C.root_lt_of_majorizes B hL hD h hne, C.root_pos, B.root_pos]
  exact mul_lt_mul_of_pos_left hs B.diffusivity_pos

theorem PlacementProblem.schur_eq_iff (C B : PlacementProblem n)
    (hL : C.length = B.length) (hD : C.diffusivity = B.diffusivity)
    (h : Majorizes C.strength B.strength) :
    C.optimalPhysical.principalValue = B.optimalPhysical.principalValue ↔
      ∃ σ : Equiv.Perm (Fin n), C.strength = B.strength ∘ σ := by
  constructor
  · intro he
    by_contra hne
    exact (C.schur_lt B hL hD h hne).ne he
  · intro hp
    rw [C.optimal_principalValue, B.optimal_principalValue, hD,
      C.root_eq_of_strength_permutation B hL hD hp]

end TimeTraps.Spectral
