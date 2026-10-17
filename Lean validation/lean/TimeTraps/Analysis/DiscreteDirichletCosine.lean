module

public import TimeTraps.Analysis.DiscreteDirichletModes
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

/-! Exact finite cosine sums on the interior Dirichlet grid, including the
even/odd and negative-frequency cases used in the manuscript. -/

namespace TimeTraps.Analysis

open scoped BigOperators

noncomputable def discreteCosineSum (n : ℕ) (m : ℤ) : ℝ :=
  ∑ j : Fin n, Real.cos ((m : ℝ) * Real.pi * ((j.val : ℝ) + 1) / ((n : ℝ) + 1))

theorem discrete_cosine_telescope (n : ℕ) (a : ℝ) :
    2 * Real.sin (a / 2) * (∑ j : Fin n, Real.cos (a * ((j.val : ℝ) + 1))) =
      Real.sin (a * ((n : ℝ) + 1 / 2)) - Real.sin (a / 2) := by
  let f : Fin (n + 1) → ℝ := fun j => Real.sin (a * ((j.val : ℝ) + 1 / 2))
  have ht (j : Fin n) : 2 * Real.sin (a / 2) * Real.cos (a * ((j.val : ℝ) + 1)) =
      f j.succ - f j.castSucc := by
    dsimp only [f]
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    have hl : a * ((j.val : ℝ) + 1 + 1 / 2) = a * ((j.val : ℝ) + 1) + a / 2 := by ring
    have hr : a * ((j.val : ℝ) + 1 / 2) = a * ((j.val : ℝ) + 1) - a / 2 := by ring
    rw [hl, hr, Real.sin_add, Real.sin_sub]
    ring
  rw [Finset.mul_sum]
  simp_rw [ht]
  rw [discrete_summation_telescope]
  simp [f, mul_add, div_eq_mul_inv]

theorem discreteCosineSum_neg (n : ℕ) (m : ℤ) :
    discreteCosineSum n (-m) = discreteCosineSum n m := by
  unfold discreteCosineSum
  apply Finset.sum_congr rfl
  intro j _
  simp only [Int.cast_neg, neg_mul, neg_div, Real.cos_neg]

theorem discreteCosineSum_zero (n : ℕ) : discreteCosineSum n 0 = n := by
  simp [discreteCosineSum]

theorem discreteCosineSum_nat (n m : ℕ) (hm : 0 < m) (hmn : m < 2 * (n + 1)) :
    discreteCosineSum n (m : ℤ) = -(1 + (-1 : ℝ) ^ m) / 2 := by
  let a : ℝ := (m : ℝ) * Real.pi / ((n : ℝ) + 1)
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) < 2 * ((n : ℝ) + 1) := by exact_mod_cast hmn
  have ha : 0 < a / 2 := div_pos (div_pos (mul_pos hmR Real.pi_pos) hn) (by norm_num)
  have haπ : a / 2 < Real.pi := by
    dsimp only [a]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2), div_lt_iff₀ hn]
    nlinarith [Real.pi_pos]
  have hs := Real.sin_pos_of_mem_Ioo ⟨ha, haπ⟩
  have ht := discrete_cosine_telescope n a
  have hsum : (∑ j : Fin n, Real.cos (a * ((j.val : ℝ) + 1))) =
      discreteCosineSum n (m : ℤ) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [Int.cast_natCast]
    congr 1
    dsimp only [a]
    ring
  have hend : a * ((n : ℝ) + 1 / 2) = (m : ℝ) * Real.pi - a / 2 := by
    dsimp only [a]
    field_simp
    ring
  rw [hsum, hend, Real.sin_nat_mul_pi_sub] at ht
  apply (mul_right_cancel₀ (ne_of_gt hs))
  nlinarith

theorem discreteCosineSum_even (n m : ℕ) (hm : 0 < m) (hmn : m < 2 * (n + 1))
    (he : Even m) : discreteCosineSum n (m : ℤ) = -1 := by
  rw [discreteCosineSum_nat n m hm hmn, he.neg_one_pow]
  norm_num

theorem discreteCosineSum_odd (n m : ℕ) (hm : 0 < m) (hmn : m < 2 * (n + 1))
    (ho : Odd m) : discreteCosineSum n (m : ℤ) = 0 := by
  rw [discreteCosineSum_nat n m hm hmn, ho.neg_one_pow]
  norm_num

theorem discreteSineVector_norm_sq {n : ℕ} (k : Fin n) :
    (∑ j, discreteSineVector n k j ^ 2) = ((n : ℝ) + 1) / 2 := by
  have hc := discreteCosineSum_even n (2 * (k.val + 1)) (by omega)
    (by have := k.isLt; omega) (even_two_mul _)
  have ht (j : Fin n) : 2 * discreteSineVector n k j ^ 2 =
      1 - Real.cos (((2 * (k.val + 1) : ℕ) : ℝ) * Real.pi *
        ((j.val : ℝ) + 1) / ((n : ℝ) + 1)) := by
    unfold discreteSineVector discreteSineMode
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat]
    have ha : 2 * ((k.val : ℝ) + 1) * Real.pi * ((j.val : ℝ) + 1) / ((n : ℝ) + 1) =
        2 * (((k.val : ℝ) + 1) * Real.pi * ((j.val : ℝ) + 1) / ((n : ℝ) + 1)) := by ring
    rw [ha, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq
      (((k.val : ℝ) + 1) * Real.pi * ((j.val : ℝ) + 1) / ((n : ℝ) + 1))]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => ht j)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hcos : (∑ j : Fin n, Real.cos (((2 * (k.val + 1) : ℕ) : ℝ) * Real.pi *
      ((j.val : ℝ) + 1) / ((n : ℝ) + 1))) = -1 := by
    simpa only [discreteCosineSum, Int.cast_natCast] using hc
  rw [hcos] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  linarith

end TimeTraps.Analysis
