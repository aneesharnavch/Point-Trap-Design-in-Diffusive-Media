module

public import TimeTraps.Analysis.DiscreteDirichletSine

@[expose] public section

/-! The sharp discrete Dirichlet Poincaré inequality. Its proof uses the
positive first sine mode, not an assumed spectral expansion. The endpoints
remain in the norm sum and vanish by hypothesis. -/

namespace TimeTraps.Analysis

open scoped BigOperators

noncomputable def discreteDirichletConstant (n : ℕ) : ℝ :=
  if n = 1 then 0 else 1 / (4 * Real.sin (Real.pi / (2 * (n : ℝ))) ^ 2)

theorem discreteDirichletConstant_one : discreteDirichletConstant 1 = 0 := by
  simp [discreteDirichletConstant]

theorem discreteDirichletConstant_eq {n : ℕ} (hn : 2 ≤ n) :
    discreteDirichletConstant n = 1 / (4 * Real.sin (Real.pi / (2 * (n : ℝ))) ^ 2) := by
  simp [discreteDirichletConstant, show n ≠ 1 by omega]

theorem discreteDirichletConstant_nonneg (n : ℕ) : 0 ≤ discreteDirichletConstant n := by
  unfold discreteDirichletConstant
  split_ifs
  · exact le_rfl
  · positivity

theorem discreteDirichletConstant_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < discreteDirichletConstant n := by
  rw [discreteDirichletConstant_eq hn]
  exact one_div_pos.mpr (discreteDirichletEigenvalue_pos (by omega))

theorem discrete_dirichlet_eigenvalue_bound {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 1) → ℝ) (h0 : s 0 = 0) (hlast : s (Fin.last n) = 0) :
    discreteDirichletEigenvalue n * (∑ i, s i ^ 2) ≤
      ∑ i : Fin n, (s i.succ - s i.castSucc) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hp (i : Fin m) : 0 < discreteDirichletSine (m + 1) i.succ.castSucc := by
    apply discreteDirichletSine_pos (by omega)
    · simp
    · exact Nat.succ_lt_succ i.isLt
  have hz (i : Fin (m + 2)) (hi : discreteDirichletSine (m + 1) i = 0) : s i = 0 := by
    by_cases hi0 : i.val = 0
    · have he : i = 0 := Fin.ext hi0
      simpa only [he] using h0
    by_cases hil : i.val = m + 1
    · have he : i = Fin.last (m + 1) := Fin.ext hil
      simpa only [he] using hlast
    have hpos := discreteDirichletSine_pos (by omega : 0 < m + 1) i
      (by omega) (by have := i.isLt; omega)
    linarith
  have hb := discrete_dirichlet_ground_bound s (discreteDirichletSine (m + 1))
    (2 * Real.cos (Real.pi / ((m : ℝ) + 1))) h0 hlast
    (discreteDirichletSine_nonneg (by omega)) hz hp discreteDirichletSine_neighbors
  rw [discreteDirichletEigenvalue_eq (by omega)]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hb

theorem discrete_dirichlet_poincare {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 1) → ℝ) (h0 : s 0 = 0) (hlast : s (Fin.last n) = 0) :
    (∑ i, s i ^ 2) ≤ discreteDirichletConstant n *
      ∑ i : Fin n, (s i.succ - s i.castSucc) ^ 2 := by
  by_cases hn1 : n = 1
  · subst n
    have hz (i : Fin 2) : s i = 0 := by
      by_cases hi : i = 0
      · simpa only [hi] using h0
      · have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
        have hiv : i.val < 2 := i.isLt
        have he : i = Fin.last 1 := Fin.ext (show i.val = 1 by omega)
        simpa only [he] using hlast
    simp [hz]
  · have hb := discrete_dirichlet_eigenvalue_bound hn s h0 hlast
    rw [discreteDirichletConstant, if_neg hn1]
    change (∑ i, s i ^ 2) ≤ 1 / discreteDirichletEigenvalue n * _
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (discreteDirichletEigenvalue_pos hn)).mpr
    simpa only [mul_comm] using hb

theorem discreteDirichletSine_mass_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < ∑ i, discreteDirichletSine n i ^ 2 := by
  let i : Fin (n + 1) := ⟨1, by omega⟩
  have hi := discreteDirichletSine_pos (by omega : 0 < n) i (by simp [i]) (by simpa [i])
  exact Finset.sum_pos' (fun j _ => sq_nonneg (discreteDirichletSine n j))
    ⟨i, Finset.mem_univ i, sq_pos_of_pos hi⟩

theorem discrete_dirichlet_poincare_attained {n : ℕ} (hn : 2 ≤ n) :
    (∑ i, discreteDirichletSine n i ^ 2) = discreteDirichletConstant n *
      ∑ i : Fin n, (discreteDirichletSine n i.succ -
        discreteDirichletSine n i.castSucc) ^ 2 := by
  rw [discreteDirichletSine_energy (by omega), discreteDirichletConstant_eq hn]
  change (∑ i, discreteDirichletSine n i ^ 2) =
    1 / discreteDirichletEigenvalue n * (discreteDirichletEigenvalue n * _)
  rw [← mul_assoc, one_div_mul_cancel (ne_of_gt (discreteDirichletEigenvalue_pos (by omega))),
    one_mul]

theorem discrete_dirichlet_poincare_constant_le {n : ℕ} (hn : 2 ≤ n) (C : ℝ)
    (hC : ∀ s : Fin (n + 1) → ℝ, s 0 = 0 → s (Fin.last n) = 0 →
      (∑ i, s i ^ 2) ≤ C * ∑ i : Fin n, (s i.succ - s i.castSucc) ^ 2) :
    discreteDirichletConstant n ≤ C := by
  have he := discreteDirichletSine_energy (by omega : 0 < n)
  have hE : 0 < ∑ i : Fin n, (discreteDirichletSine n i.succ -
      discreteDirichletSine n i.castSucc) ^ 2 := by
    rw [he]
    exact mul_pos (discreteDirichletEigenvalue_pos (by omega)) (discreteDirichletSine_mass_pos hn)
  have hc := hC (discreteDirichletSine n) (discreteDirichletSine_zero _)
    (discreteDirichletSine_last (by omega))
  rw [discrete_dirichlet_poincare_attained hn] at hc
  exact (mul_le_mul_iff_left₀ hE).mp hc

end TimeTraps.Analysis
