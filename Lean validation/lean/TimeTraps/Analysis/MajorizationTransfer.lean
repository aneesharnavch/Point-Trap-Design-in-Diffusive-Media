module

public import TimeTraps.Analysis.Majorization
public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Relation
public import Mathlib.Tactic

@[expose] public section

/-! A balancing transfer moves positive mass from a larger coordinate to a
smaller one without reversing their order. The relations below record actual
finite sequences of such transfers and permutations. -/

namespace TimeTraps.Analysis

open scoped BigOperators

variable {n : ℕ}

noncomputable def balance (x : Fin n → ℝ) (i j : Fin n) (ε : ℝ) (k : Fin n) : ℝ :=
  x k - (if k = i then ε else 0) + (if k = j then ε else 0)

def BalancingStep (x z : Fin n → ℝ) : Prop :=
  ∃ i j ε, i ≠ j ∧ 0 < ε ∧ 2 * ε ≤ x i - x j ∧ z = balance x i j ε

def BalancingChain (x y : Fin n → ℝ) : Prop := Relation.ReflTransGen BalancingStep x y

def MajorizationTransferStep (x y : Fin n → ℝ) : Prop :=
  BalancingStep x y ∨ ∃ σ : Equiv.Perm (Fin n), y = x ∘ σ

def MajorizationTransferChain (x y : Fin n → ℝ) : Prop :=
  Relation.ReflTransGen MajorizationTransferStep x y

theorem balance_donor (x : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) (ε : ℝ) :
    balance x i j ε i = x i - ε := by simp [balance, hij]

theorem balance_receiver (x : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) (ε : ℝ) :
    balance x i j ε j = x j + ε := by simp [balance, hij.symm]

theorem balance_other (x : Fin n → ℝ) {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j)
    (ε : ℝ) : balance x i j ε k = x k := by simp [balance, hki, hkj]

theorem vectorPrefix_balance (x : Fin n → ℝ) (i j : Fin n) (ε : ℝ) (k : ℕ) :
    vectorPrefix (balance x i j ε) k = vectorPrefix x k -
      (if i.val < k then ε else 0) + (if j.val < k then ε else 0) := by
  classical
  have hs (l : Fin n) : (if l.val < k then balance x i j ε l else 0) =
      (if l.val < k then x l else 0) -
        (if l = i then (if i.val < k then ε else 0) else 0) +
        (if l = j then (if j.val < k then ε else 0) else 0) := by
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
      by_cases hlk : l.val < k <;> simp_all [balance] <;> split_ifs <;> simp_all
  unfold vectorPrefix
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp

theorem balance_sum (x : Fin n → ℝ) (i j : Fin n) (ε : ℝ) :
    (∑ k, balance x i j ε k) = ∑ k, x k := by
  have hs := vectorPrefix_balance x i j ε n
  simpa only [vectorPrefix_total, i.isLt, j.isLt, if_true, sub_add_cancel] using hs

noncomputable def mismatchCount (x y : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

theorem balance_mismatchCount_lt (x y : Fin n → ℝ) {i j : Fin n}
    (hij : i ≠ j) (hi : y i < x i) (hj : x j < y j) :
    mismatchCount (balance x i j (min (x i - y i) (y j - x j))) y < mismatchCount x y := by
  classical
  let ε := min (x i - y i) (y j - x j)
  let T := Finset.univ.filter fun k => x k ≠ y k
  let U := Finset.univ.filter fun k => balance x i j ε k ≠ y k
  have hsub : U ⊆ T := by
    intro k hk
    have hne := (Finset.mem_filter.mp hk).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ k, ?_⟩
    by_cases hki : k = i
    · subst k; exact hi.ne'
    by_cases hkj : k = j
    · subst k; exact hj.ne
    simpa only [balance_other x hki hkj ε] using hne
  have hmissing : ∃ k ∈ T, k ∉ U := by
    rcases le_total (x i - y i) (y j - x j) with h | h
    · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.ne'⟩, ?_⟩
      have he : balance x i j ε i = y i := by
        rw [balance_donor x hij, show ε = x i - y i from min_eq_left h]
        ring
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, he, ne_eq,
        not_true_eq_false, not_false_eq_true]
    · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.ne⟩, ?_⟩
      have he : balance x i j ε j = y j := by
        rw [balance_receiver x hij, show ε = y j - x j from min_eq_right h]
        ring
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, he, ne_eq,
        not_true_eq_false, not_false_eq_true]
  have hproper : U ⊂ T := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro he
    obtain ⟨k, hk, hku⟩ := hmissing
    exact hku (he.symm ▸ hk)
  exact Finset.card_lt_card hproper

theorem balance_prefix_preserves (x y : Fin n → ℝ) {i j : Fin n} (hij : i < j)
    (hbefore : ∀ k, k < j → y k ≤ x k) {ε : ℝ} (hε : ε ≤ x i - y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) :
    ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix (balance x i j ε) k := by
  intro k hk
  rw [vectorPrefix_balance]
  by_cases hjk : j.val < k
  · have hik : i.val < k := lt_trans hij hjk
    simpa only [hik, hjk, if_true, sub_add_cancel] using hp k hk
  by_cases hik : i.val < k
  · simp only [hik, hjk, if_true, if_false, add_zero]
    have hd : x i - y i ≤ vectorPrefix (fun l => x l - y l) k := by
      unfold vectorPrefix
      have hnonneg : ∀ l ∈ Finset.univ, 0 ≤ (if l.val < k then x l - y l else 0) := by
        intro l _
        split_ifs with hl
        · exact sub_nonneg.mpr (hbefore l (show l < j by omega))
        · exact le_rfl
      simpa only [hik, if_true] using
        (Finset.single_le_sum hnonneg (Finset.mem_univ i))
    rw [vectorPrefix_sub] at hd
    linarith
  · simpa only [hik, hjk, if_false, sub_zero, add_zero] using hp k hk

end TimeTraps.Analysis
