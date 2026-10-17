module

public import TimeTraps.Analysis.DiscreteDirichletBasis

@[expose] public section

/-! Reconstruction on the endpoint-inclusive path and the exact diagonal
energy formula in normalized sine coefficients. -/

namespace TimeTraps.Analysis

open scoped BigOperators

noncomputable def discreteNormalizedMode (n : ℕ) (k : Fin n) (j : Fin (n + 2)) : ℝ :=
  Real.sqrt (2 / ((n : ℝ) + 1)) * discreteSineMode n k j

theorem discreteNormalizedMode_zero {n : ℕ} (k : Fin n) :
    discreteNormalizedMode n k 0 = 0 := by
  simp [discreteNormalizedMode, discreteSineMode_zero]

theorem discreteNormalizedMode_last {n : ℕ} (k : Fin n) :
    discreteNormalizedMode n k (Fin.last (n + 1)) = 0 := by
  simp [discreteNormalizedMode, discreteSineMode_last]

theorem discreteNormalizedMode_interior {n : ℕ} (k j : Fin n) :
    discreteNormalizedMode n k j.succ.castSucc = discreteNormalizedSine n k j := rfl

theorem discreteNormalizedMode_eigenvector {n : ℕ} (k j : Fin n) :
    discreteSecondDifference (discreteNormalizedMode n k) j =
      discreteSineEigenvalue n k * discreteNormalizedSine n k j := by
  calc
    _ = Real.sqrt (2 / ((n : ℝ) + 1)) *
        discreteSecondDifference (discreteSineMode n k) j := by
      unfold discreteSecondDifference discreteNormalizedMode
      ring
    _ = _ := by
      rw [discreteSineMode_eigenvector]
      unfold discreteNormalizedSine
      ring

theorem discrete_sine_full_expansion {n : ℕ} (s : Fin (n + 2) → ℝ)
    (h0 : s 0 = 0) (hlast : s (Fin.last (n + 1)) = 0) (j : Fin (n + 2)) :
    (∑ k, discreteSineCoefficient (fun i : Fin n => s i.succ.castSucc) k *
      discreteNormalizedMode n k j) = s j := by
  by_cases hj0 : j.val = 0
  · have he : j = 0 := Fin.ext hj0
    simp [he, h0, discreteNormalizedMode_zero]
  by_cases hjlast : j.val = n + 1
  · have he : j = Fin.last (n + 1) := Fin.ext hjlast
    simp [he, hlast, discreteNormalizedMode_last]
  let i : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
  have he : j = i.succ.castSucc := by
    apply Fin.ext
    change j.val = j.val - 1 + 1
    omega
  rw [he]
  simp only [discreteNormalizedMode_interior]
  exact discrete_sine_expansion (fun i : Fin n => s i.succ.castSucc) i

theorem discrete_second_difference_expansion {n : ℕ} (s : Fin (n + 2) → ℝ)
    (h0 : s 0 = 0) (hlast : s (Fin.last (n + 1)) = 0) (j : Fin n) :
    discreteSecondDifference s j = ∑ k,
      discreteSineCoefficient (fun i : Fin n => s i.succ.castSucc) k *
        discreteSineEigenvalue n k * discreteNormalizedSine n k j := by
  unfold discreteSecondDifference
  rw [← discrete_sine_full_expansion s h0 hlast j.succ.castSucc,
    ← discrete_sine_full_expansion s h0 hlast j.castSucc.castSucc,
    ← discrete_sine_full_expansion s h0 hlast j.succ.succ]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = discreteSineCoefficient (fun i : Fin n => s i.succ.castSucc) k *
        discreteSecondDifference (discreteNormalizedMode n k) j := by
      unfold discreteSecondDifference
      ring
    _ = _ := by rw [discreteNormalizedMode_eigenvector]; ring

theorem discrete_sine_energy_diagonalization {n : ℕ} (s : Fin (n + 2) → ℝ)
    (h0 : s 0 = 0) (hlast : s (Fin.last (n + 1)) = 0) :
    (∑ i : Fin (n + 1), (s i.succ - s i.castSucc) ^ 2) =
      ∑ k, discreteSineEigenvalue n k *
        discreteSineCoefficient (fun j : Fin n => s j.succ.castSucc) k ^ 2 := by
  rw [discrete_dirichlet_energy_second_difference s h0 hlast]
  simp_rw [discrete_second_difference_expansion s h0 hlast, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = discreteSineEigenvalue n k *
        discreteSineCoefficient (fun j : Fin n => s j.succ.castSucc) k *
        ∑ j : Fin n, s j.succ.castSucc * discreteNormalizedSine n k j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      change discreteSineEigenvalue n k *
          discreteSineCoefficient (fun j : Fin n => s j.succ.castSucc) k *
          discreteSineCoefficient (fun j : Fin n => s j.succ.castSucc) k = _
      ring

theorem discreteSineEigenvalue_first {n : ℕ} (hn : 0 < n) :
    discreteSineEigenvalue n ⟨0, hn⟩ = discreteDirichletEigenvalue (n + 1) := by
  simp [discreteSineEigenvalue, discreteDirichletEigenvalue]

theorem discreteSineEigenvalue_lower {n : ℕ} (hn : 0 < n) (k : Fin n) :
    discreteDirichletEigenvalue (n + 1) ≤ discreteSineEigenvalue n k := by
  rw [← discreteSineEigenvalue_first hn]
  exact (discreteSineEigenvalue_strictMono n).monotone (by exact Nat.zero_le k.val)

end TimeTraps.Analysis
