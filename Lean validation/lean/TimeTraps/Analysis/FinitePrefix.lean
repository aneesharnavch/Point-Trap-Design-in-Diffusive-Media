module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Finite partial sums and exact summation by parts. Positive partial sums
with zero total pair nonpositively with increasing coefficients. -/

namespace TimeTraps.Analysis

open scoped BigOperators

variable {n : ℕ}

noncomputable def vectorPrefix (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if i.val < k then x i else 0

theorem vectorPrefix_zero (x : Fin n → ℝ) : vectorPrefix x 0 = 0 := by
  simp [vectorPrefix]

theorem vectorPrefix_total (x : Fin n → ℝ) : vectorPrefix x n = ∑ i, x i := by
  simp [vectorPrefix]

theorem vectorPrefix_succ (x : Fin n → ℝ) (i : Fin n) :
    vectorPrefix x (i.val + 1) = vectorPrefix x i.val + x i := by
  have hi (j : Fin n) : (if j.val < i.val + 1 then x j else 0) =
      (if j.val < i.val then x j else 0) + (if j = i then x j else 0) := by
    by_cases hlt : j.val < i.val
    · have hne : j ≠ i := by intro he; subst j; omega
      simp [hlt, hne, show j.val < i.val + 1 by omega]
    · by_cases he : j = i
      · subst j
        simp
      · have hn : ¬ j.val < i.val + 1 := by
          have hv : j.val ≠ i.val := fun h => he (Fin.ext h)
          omega
        simp [hlt, he, hn]
  unfold vectorPrefix
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp

theorem vectorPrefix_sub (x y : Fin n → ℝ) (k : ℕ) :
    vectorPrefix (fun i => x i - y i) k = vectorPrefix x k - vectorPrefix y k := by
  unfold vectorPrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

theorem finite_summation_by_parts (a d : Fin (n + 1) → ℝ) :
    (∑ i, a i * d i) = a (Fin.last n) * vectorPrefix d (n + 1) -
      ∑ i : Fin n, (a i.succ - a i.castSucc) * vectorPrefix d (i.val + 1) := by
  have hd (i : Fin (n + 1)) : d i = vectorPrefix d (i.val + 1) - vectorPrefix d i.val := by
    linarith [vectorPrefix_succ d i]
  conv_lhs => arg 2; ext i; rw [hd i, mul_sub]
  rw [Finset.sum_sub_distrib,
    Fin.sum_univ_castSucc (fun i : Fin (n + 1) => a i * vectorPrefix d (i.val + 1)),
    Fin.sum_univ_succ (fun i : Fin (n + 1) => a i * vectorPrefix d i.val)]
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero,
    vectorPrefix_zero, mul_zero, zero_add]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

theorem weighted_sum_nonpos_of_prefix (a d : Fin n → ℝ) (ha : Monotone a)
    (htotal : (∑ i, d i) = 0) (hp : ∀ k ≤ n, 0 ≤ vectorPrefix d k) :
    (∑ i, a i * d i) ≤ 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [finite_summation_by_parts, vectorPrefix_total, htotal, mul_zero, zero_sub]
    apply neg_nonpos.mpr
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (sub_nonneg.mpr (ha Fin.castSucc_lt_succ.le))
      (hp (i.val + 1) (by omega))

end TimeTraps.Analysis
