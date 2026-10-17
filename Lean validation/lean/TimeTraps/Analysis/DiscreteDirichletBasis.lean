module

public import TimeTraps.Analysis.DiscreteDirichletOrthogonality
public import Mathlib.LinearAlgebra.StdBasis

@[expose] public section

/-! The normalized sine basis and its explicit inverse transform. Symmetry
of the square sine array turns row orthogonality into completeness. -/

namespace TimeTraps.Analysis

open scoped BigOperators

noncomputable def discreteSineCoefficient {n : ℕ} (s : Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ j, s j * discreteNormalizedSine n k j

theorem discreteNormalizedSine_complete {n : ℕ} (i j : Fin n) :
    (∑ k, discreteNormalizedSine n k i * discreteNormalizedSine n k j) =
      if i = j then 1 else 0 := by
  calc
    _ = ∑ k, discreteNormalizedSine n i k * discreteNormalizedSine n j k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [discreteNormalizedSine_symmetric k i, discreteNormalizedSine_symmetric k j]
    _ = _ := discreteNormalizedSine_orthonormal i j

theorem discrete_sine_expansion {n : ℕ} (s : Fin n → ℝ) (j : Fin n) :
    (∑ k, discreteSineCoefficient s k * discreteNormalizedSine n k j) = s j := by
  unfold discreteSineCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, s i * ∑ k, discreteNormalizedSine n k i * discreteNormalizedSine n k j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by simp_rw [discreteNormalizedSine_complete]; simp

theorem discreteSineCoefficient_involutive {n : ℕ} (s : Fin n → ℝ) :
    discreteSineCoefficient (discreteSineCoefficient s) = s := by
  funext j
  change (∑ k, discreteSineCoefficient s k * discreteNormalizedSine n j k) = s j
  have he := discrete_sine_expansion s j
  have hs : (∑ k, discreteSineCoefficient s k * discreteNormalizedSine n j k) =
      ∑ k, discreteSineCoefficient s k * discreteNormalizedSine n k j := by
    apply Finset.sum_congr rfl
    intro k _
    rw [discreteNormalizedSine_symmetric j k]
  exact hs.trans he

noncomputable def discreteSineTransform (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := discreteSineCoefficient
  invFun := discreteSineCoefficient
  left_inv := discreteSineCoefficient_involutive
  right_inv := discreteSineCoefficient_involutive
  map_add' s t := by
    funext k
    simp [discreteSineCoefficient, add_mul, Finset.sum_add_distrib]
  map_smul' c s := by
    funext k
    simp [discreteSineCoefficient, Finset.mul_sum, mul_assoc]

noncomputable def discreteSineBasis (n : ℕ) : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map (discreteSineTransform n)

theorem discreteSineBasis_apply {n : ℕ} (k j : Fin n) :
    discreteSineBasis n k j = discreteNormalizedSine n k j := by
  rw [discreteSineBasis, Module.Basis.map_apply]
  change discreteSineCoefficient (Pi.basisFun ℝ (Fin n) k) j = _
  simp [discreteSineCoefficient, Pi.basisFun_apply, Pi.single_apply,
    discreteNormalizedSine_symmetric j k]

theorem discreteSineBasis_orthonormal {n : ℕ} (k l : Fin n) :
    (∑ j, discreteSineBasis n k j * discreteSineBasis n l j) =
      if k = l then 1 else 0 := by
  simp only [discreteSineBasis_apply]
  exact discreteNormalizedSine_orthonormal k l

theorem discrete_sine_expansion_unique {n : ℕ} (s : Fin n → ℝ) :
    ∃! c : Fin n → ℝ, ∀ j, s j = ∑ k, c k * discreteNormalizedSine n k j := by
  refine ⟨discreteSineCoefficient s, fun j => (discrete_sine_expansion s j).symm, ?_⟩
  intro c hc
  have hs : s = discreteSineCoefficient c := by
    funext j
    rw [hc j]
    unfold discreteSineCoefficient
    apply Finset.sum_congr rfl
    intro k _
    rw [discreteNormalizedSine_symmetric k j]
  rw [hs, discreteSineCoefficient_involutive]

theorem discrete_sine_parseval {n : ℕ} (s : Fin n → ℝ) :
    (∑ j, s j ^ 2) = ∑ k, discreteSineCoefficient s k ^ 2 := by
  calc
    _ = ∑ j, s j * ∑ k, discreteSineCoefficient s k * discreteNormalizedSine n k j := by
      simp_rw [discrete_sine_expansion]
      simp only [pow_two]
    _ = ∑ k, discreteSineCoefficient s k * ∑ j, s j * discreteNormalizedSine n k j := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp only [discreteSineCoefficient, pow_two]

end TimeTraps.Analysis
