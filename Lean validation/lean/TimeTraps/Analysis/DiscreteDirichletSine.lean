module

public import TimeTraps.Analysis.DiscreteDirichletEnergy
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-! The positive first sine mode on a finite Dirichlet path, its exact
second-difference eigenvalue, and its energy. -/

namespace TimeTraps.Analysis

open scoped BigOperators

noncomputable def discreteDirichletSine (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  Real.sin (Real.pi * (i.val : ℝ) / (n : ℝ))

noncomputable def discreteDirichletEigenvalue (n : ℕ) : ℝ :=
  4 * Real.sin (Real.pi / (2 * (n : ℝ))) ^ 2

theorem discreteDirichletSine_zero (n : ℕ) : discreteDirichletSine n 0 = 0 := by
  simp [discreteDirichletSine]

theorem discreteDirichletSine_last {n : ℕ} (hn : 0 < n) :
    discreteDirichletSine n (Fin.last n) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [discreteDirichletSine, mul_div_cancel_right₀ _ hnR]

theorem discreteDirichletSine_pos {n : ℕ} (hn : 0 < n) (i : Fin (n + 1))
    (hi0 : 0 < i.val) (hin : i.val < n) : 0 < discreteDirichletSine n i := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hiR : 0 < (i.val : ℝ) := by exact_mod_cast hi0
  have hinR : (i.val : ℝ) < n := by exact_mod_cast hin
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · exact div_pos (mul_pos Real.pi_pos hiR) hnR
  · apply (div_lt_iff₀ hnR).mpr
    nlinarith [Real.pi_pos]

theorem discreteDirichletSine_nonneg {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    0 ≤ discreteDirichletSine n i := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hiR : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hinR : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  apply Real.sin_nonneg_of_mem_Icc
  constructor
  · exact div_nonneg (mul_nonneg Real.pi_pos.le hiR) hnR.le
  · apply (div_le_iff₀ hnR).mpr
    nlinarith [Real.pi_pos]

theorem discreteDirichletSine_neighbors {n : ℕ} (i : Fin n) :
    discreteDirichletSine (n + 1) i.castSucc.castSucc +
        discreteDirichletSine (n + 1) i.succ.succ =
      (2 * Real.cos (Real.pi / ((n : ℝ) + 1))) *
        discreteDirichletSine (n + 1) i.succ.castSucc := by
  simp only [discreteDirichletSine, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one]
  have hl : Real.pi * (i.val : ℝ) / ((n : ℝ) + 1) =
      Real.pi * ((i.val : ℝ) + 1) / ((n : ℝ) + 1) -
        Real.pi / ((n : ℝ) + 1) := by ring
  have hr : Real.pi * (((i.val : ℝ) + 1) + 1) / ((n : ℝ) + 1) =
      Real.pi * ((i.val : ℝ) + 1) / ((n : ℝ) + 1) +
        Real.pi / ((n : ℝ) + 1) := by ring
  rw [hl, hr, Real.sin_sub, Real.sin_add]
  ring

theorem discreteDirichletEigenvalue_eq {n : ℕ} (hn : 0 < n) :
    discreteDirichletEigenvalue n = 2 - 2 * Real.cos (Real.pi / (n : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hangle : Real.pi / (n : ℝ) = 2 * (Real.pi / (2 * (n : ℝ))) := by
    field_simp
  rw [hangle, Real.cos_two_mul]
  unfold discreteDirichletEigenvalue
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi / (2 * (n : ℝ)))]

theorem discreteDirichletEigenvalue_pos {n : ℕ} (hn : 0 < n) :
    0 < discreteDirichletEigenvalue n := by
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < 2 * (n : ℝ) := by linarith
  have hs : 0 < Real.sin (Real.pi / (2 * (n : ℝ))) := by
    apply Real.sin_pos_of_mem_Ioo
    refine ⟨div_pos Real.pi_pos hd, ?_⟩
    apply (div_lt_iff₀ hd).mpr
    nlinarith [Real.pi_pos]
  exact mul_pos (by norm_num) (sq_pos_of_pos hs)

theorem discreteDirichletSine_energy {n : ℕ} (hn : 0 < n) :
    (∑ i : Fin n, (discreteDirichletSine n i.succ -
      discreteDirichletSine n i.castSucc) ^ 2) =
      discreteDirichletEigenvalue n * ∑ i, discreteDirichletSine n i ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hp (i : Fin m) : 0 < discreteDirichletSine (m + 1) i.succ.castSucc := by
    apply discreteDirichletSine_pos (by omega)
    · simp
    · exact Nat.succ_lt_succ i.isLt
  have he := discrete_dirichlet_ground_energy (discreteDirichletSine (m + 1))
    (2 * Real.cos (Real.pi / ((m : ℝ) + 1)))
    (discreteDirichletSine_zero _) (discreteDirichletSine_last (by omega))
    hp discreteDirichletSine_neighbors
  rw [discreteDirichletEigenvalue_eq (by omega)]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using he

end TimeTraps.Analysis
