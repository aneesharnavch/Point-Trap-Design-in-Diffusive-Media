module

public import TimeTraps.Analysis.MajorizationTransfer

@[expose] public section

/-! Constructing a finite balancing chain. At the first deficit coordinate,
an earlier surplus supplies a transfer which fixes at least one coordinate.
Induction on the number of mismatches terminates without a sorting assumption
on intermediate vectors. -/

namespace TimeTraps.Analysis

open scoped BigOperators

variable {n : ℕ}

theorem first_deficit_exists {x y : Fin n → ℝ}
    (htotal : (∑ i, x i) = ∑ i, y i) (hne : x ≠ y) :
    ∃ j, x j < y j ∧ ∀ k, k < j → y k ≤ x k := by
  classical
  have hex : ∃ j, x j < y j := by
    by_contra h
    have hle : ∀ i, y i ≤ x i := fun i => le_of_not_gt (fun hi => h ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := not_forall.mp (show ¬ ∀ i, x i = y i from fun he => hne (funext he))
    have hs := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => hle j)
      ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hle i) (Ne.symm hi)⟩
    linarith
  let T := Finset.univ.filter fun j => x j < y j
  have hT : T.Nonempty := by
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  refine ⟨T.min' hT, (Finset.mem_filter.mp (T.min'_mem hT)).2, ?_⟩
  intro k hk
  by_contra h
  have hmem : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ k, lt_of_not_ge h⟩
  exact (T.min'_le k hmem).not_gt hk

theorem surplus_before_deficit {x y : Fin n → ℝ} {j : Fin n} (hj : x j < y j)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) :
    ∃ i, i < j ∧ y i < x i := by
  have hs := hp (j.val + 1) (Nat.succ_le_of_lt j.isLt)
  rw [vectorPrefix_succ, vectorPrefix_succ] at hs
  have hstrict : vectorPrefix y j.val < vectorPrefix x j.val := by linarith
  by_contra h
  have hle : vectorPrefix x j.val ≤ vectorPrefix y j.val := by
    unfold vectorPrefix
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · exact le_of_not_gt (fun hxi => h ⟨i, hi, hxi⟩)
    · exact le_rfl
  exact hstrict.not_ge hle

theorem balancing_progress_of_prefix (x y : Fin n → ℝ) (hanti : Antitone y)
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) (hne : x ≠ y) :
    ∃ z, BalancingStep x z ∧ (∑ i, z i) = ∑ i, y i ∧
      (∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix z k) ∧
      mismatchCount z y < mismatchCount x y := by
  obtain ⟨j, hj, hbefore⟩ := first_deficit_exists htotal hne
  obtain ⟨i, hij, hi⟩ := surplus_before_deficit hj hp
  let ε := min (x i - y i) (y j - x j)
  have hε : 0 < ε := lt_min (sub_pos.mpr hi) (sub_pos.mpr hj)
  have hεi : ε ≤ x i - y i := min_le_left _ _
  have hεj : ε ≤ y j - x j := min_le_right _ _
  have hbal : 2 * ε ≤ x i - x j := by
    have hyij := hanti hij.le
    linarith
  refine ⟨balance x i j ε, ⟨i, j, ε, hij.ne, hε, hbal, rfl⟩, ?_, ?_, ?_⟩
  · exact (balance_sum x i j ε).trans htotal
  · exact balance_prefix_preserves x y hij hbefore hεi hp
  · exact balance_mismatchCount_lt x y hij.ne hi hj

theorem balancingChain_of_prefix (x y : Fin n → ℝ) (hanti : Antitone y)
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hp : ∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix x k) : BalancingChain x y := by
  suffices hall : ∀ N, ∀ z : Fin n → ℝ, mismatchCount z y = N →
      (∑ i, z i) = ∑ i, y i →
      (∀ k ≤ n, vectorPrefix y k ≤ vectorPrefix z k) → BalancingChain z y from
    hall _ x rfl htotal hp
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro z hN ht hpz
    by_cases he : z = y
    · subst z
      exact Relation.ReflTransGen.refl
    obtain ⟨w, hstep, htw, hpw, hcount⟩ := balancing_progress_of_prefix z y hanti ht hpz he
    exact Relation.ReflTransGen.head hstep
      (ih _ (hcount.trans_eq hN) w rfl htw hpw)

theorem BalancingChain.to_transferChain {x y : Fin n → ℝ} (h : BalancingChain x y) :
    MajorizationTransferChain x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (Or.inl hstep)

theorem Majorizes.transferChain {x y : Fin n → ℝ} (h : Majorizes x y) :
    MajorizationTransferChain x y := by
  have hbalance : BalancingChain (descending x) (descending y) :=
    balancingChain_of_prefix _ _ (descending_antitone y)
      (by rw [descending_sum, descending_sum]; exact h.total) h.prefix_le
  have hfirst : MajorizationTransferStep x (descending x) :=
    Or.inr ⟨descendingOrder x, rfl⟩
  have hlast : MajorizationTransferStep (descending y) y := by
    refine Or.inr ⟨(descendingOrder y).symm, ?_⟩
    funext i
    simp [descending]
  exact Relation.ReflTransGen.head hfirst (hbalance.to_transferChain.tail hlast)

end TimeTraps.Analysis
