module

public import TimeTraps.Analysis.DiscreteDirichletSine

@[expose] public section

/-! All sine modes and discrete integration by parts. The interior dimension
is n, so the path has n + 1 gaps and n + 2 endpoint-inclusive nodes. -/

namespace TimeTraps.Analysis

open scoped BigOperators

noncomputable def discreteSineMode (n : ℕ) (k : Fin n) (j : Fin (n + 2)) : ℝ :=
  Real.sin (((k.val : ℝ) + 1) * Real.pi * (j.val : ℝ) / ((n : ℝ) + 1))

noncomputable def discreteSineVector (n : ℕ) (k j : Fin n) : ℝ :=
  discreteSineMode n k j.succ.castSucc

noncomputable def discreteSineEigenvalue (n : ℕ) (k : Fin n) : ℝ :=
  4 * Real.sin (((k.val : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) ^ 2

def discreteSecondDifference {n : ℕ} (s : Fin (n + 2) → ℝ) (i : Fin n) : ℝ :=
  2 * s i.succ.castSucc - s i.castSucc.castSucc - s i.succ.succ

theorem discrete_summation_telescope {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  have hl := Fin.sum_univ_castSucc f
  have hr := Fin.sum_univ_succ f
  rw [Finset.sum_sub_distrib]
  linarith

theorem discrete_dirichlet_summation_by_parts {n : ℕ} (s t : Fin (n + 2) → ℝ)
    (h0 : s 0 = 0) (hlast : s (Fin.last (n + 1)) = 0) :
    (∑ i : Fin (n + 1), (s i.succ - s i.castSucc) * (t i.succ - t i.castSucc)) =
      ∑ i : Fin n, s i.succ.castSucc * discreteSecondDifference t i := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc (fun i : Fin (n + 1) => s i.succ * (t i.succ - t i.castSucc)),
    Fin.sum_univ_succ (fun i : Fin (n + 1) => s i.castSucc * (t i.succ - t i.castSucc))]
  simp only [Fin.succ_last, Fin.castSucc_zero, h0, hlast, zero_mul, add_zero,
    zero_add, Fin.castSucc_succ]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [discreteSecondDifference, Fin.castSucc_succ]
  ring

theorem discrete_dirichlet_energy_second_difference {n : ℕ} (s : Fin (n + 2) → ℝ)
    (h0 : s 0 = 0) (hlast : s (Fin.last (n + 1)) = 0) :
    (∑ i : Fin (n + 1), (s i.succ - s i.castSucc) ^ 2) =
      ∑ i : Fin n, s i.succ.castSucc * discreteSecondDifference s i := by
  simpa only [pow_two] using discrete_dirichlet_summation_by_parts s s h0 hlast

theorem discreteSineMode_zero {n : ℕ} (k : Fin n) : discreteSineMode n k 0 = 0 := by
  simp [discreteSineMode]

theorem discreteSineMode_last {n : ℕ} (k : Fin n) :
    discreteSineMode n k (Fin.last (n + 1)) = 0 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [discreteSineMode, Fin.val_last, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel_right₀ _ hn]
  simpa only [Nat.cast_add, Nat.cast_one] using Real.sin_nat_mul_pi (k.val + 1)

theorem discreteSineMode_neighbors {n : ℕ} (k i : Fin n) :
    discreteSineMode n k i.castSucc.castSucc + discreteSineMode n k i.succ.succ =
      2 * Real.cos (((k.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) *
        discreteSineVector n k i := by
  simp only [discreteSineMode, discreteSineVector, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one]
  have hl : ((k.val : ℝ) + 1) * Real.pi * (i.val : ℝ) / ((n : ℝ) + 1) =
      ((k.val : ℝ) + 1) * Real.pi * ((i.val : ℝ) + 1) / ((n : ℝ) + 1) -
        ((k.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) := by ring
  have hr : ((k.val : ℝ) + 1) * Real.pi * (((i.val : ℝ) + 1) + 1) / ((n : ℝ) + 1) =
      ((k.val : ℝ) + 1) * Real.pi * ((i.val : ℝ) + 1) / ((n : ℝ) + 1) +
        ((k.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) := by ring
  rw [hl, hr, Real.sin_sub, Real.sin_add]
  ring

theorem discreteSineEigenvalue_eq {n : ℕ} (k : Fin n) :
    discreteSineEigenvalue n k =
      2 - 2 * Real.cos (((k.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)) := by
  have ha : ((k.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1) =
      2 * (((k.val : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1))) := by field_simp
  rw [ha, Real.cos_two_mul]
  unfold discreteSineEigenvalue
  nlinarith [Real.sin_sq_add_cos_sq
    (((k.val : ℝ) + 1) * Real.pi / (2 * ((n : ℝ) + 1)))]

theorem discreteSineMode_eigenvector {n : ℕ} (k i : Fin n) :
    discreteSecondDifference (discreteSineMode n k) i =
      discreteSineEigenvalue n k * discreteSineVector n k i := by
  have he := discreteSineMode_neighbors k i
  rw [discreteSineEigenvalue_eq]
  change 2 * discreteSineVector n k i - _ - _ = _
  nlinarith

theorem discreteSineVector_symmetric {n : ℕ} (k j : Fin n) :
    discreteSineVector n k j = discreteSineVector n j k := by
  unfold discreteSineVector discreteSineMode
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

end TimeTraps.Analysis
