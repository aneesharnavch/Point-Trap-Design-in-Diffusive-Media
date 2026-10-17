module

public import TimeTraps.Analysis.MajorizationTransferConstruction
public import TimeTraps.Analysis.MajorizationTransferConvex

@[expose] public section

/-! The finite Hardy--Littlewood--Pólya characterization, using the existing
decreasing-sort prefix definition of majorization. Every majorized vector is
obtained by finitely many non-crossing balancing transfers followed by one
permutation. The converse also holds. -/

namespace TimeTraps.Analysis

variable {n : ℕ}

theorem MajorizationTransferStep.majorizes {x y : Fin n → ℝ}
    (h : MajorizationTransferStep x y) : Majorizes x y := by
  rcases h with hbal | ⟨σ, rfl⟩
  · exact hbal.majorizes
  · apply Majorizes.of_permuted
    refine ⟨σ.symm, ?_⟩
    funext i
    simp

theorem MajorizationTransferChain.majorizes {x y : Fin n → ℝ}
    (h : MajorizationTransferChain x y) : Majorizes x y := by
  induction h with
  | refl => exact Majorizes.refl _
  | tail _ hstep ih => exact ih.trans hstep.majorizes

theorem majorizes_iff_transferChain (x y : Fin n → ℝ) :
    Majorizes x y ↔ MajorizationTransferChain x y :=
  ⟨Majorizes.transferChain, MajorizationTransferChain.majorizes⟩

theorem balance_comp_perm (x : Fin n → ℝ) (i j : Fin n) (ε : ℝ)
    (σ : Equiv.Perm (Fin n)) :
    balance x i j ε ∘ σ = balance (x ∘ σ) (σ.symm i) (σ.symm j) ε := by
  funext k
  have hi : σ k = i ↔ k = σ.symm i := (Equiv.eq_symm_apply σ).symm
  have hj : σ k = j ↔ k = σ.symm j := (Equiv.eq_symm_apply σ).symm
  simp only [Function.comp_apply, balance, hi, hj]

theorem BalancingStep.comp_perm {x y : Fin n → ℝ} (h : BalancingStep x y)
    (σ : Equiv.Perm (Fin n)) : BalancingStep (x ∘ σ) (y ∘ σ) := by
  obtain ⟨i, j, ε, hij, hε, hbal, rfl⟩ := h
  refine ⟨σ.symm i, σ.symm j, ε, fun he => hij (σ.symm.injective he), hε, ?_, ?_⟩
  · simpa using hbal
  · exact balance_comp_perm x i j ε σ

theorem BalancingChain.comp_perm {x y : Fin n → ℝ} (h : BalancingChain x y)
    (σ : Equiv.Perm (Fin n)) : BalancingChain (x ∘ σ) (y ∘ σ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (hstep.comp_perm σ)

theorem Majorizes.exists_balancingChain_permuted {x y : Fin n → ℝ} (h : Majorizes x y) :
    ∃ σ : Equiv.Perm (Fin n), BalancingChain x (y ∘ σ) := by
  have hbalance : BalancingChain (descending x) (descending y) :=
    balancingChain_of_prefix _ _ (descending_antitone y)
      (by rw [descending_sum, descending_sum]; exact h.total) h.prefix_le
  have hc := hbalance.comp_perm (descendingOrder x).symm
  have hx : descending x ∘ (descendingOrder x).symm = x := by
    funext i
    simp [descending]
  rw [hx] at hc
  exact ⟨(descendingOrder x).symm.trans (descendingOrder y), hc⟩

theorem majorizes_iff_balancingChain_permuted (x y : Fin n → ℝ) :
    Majorizes x y ↔ ∃ σ : Equiv.Perm (Fin n), BalancingChain x (y ∘ σ) := by
  constructor
  · exact Majorizes.exists_balancingChain_permuted
  · rintro ⟨σ, h⟩
    exact h.to_transferChain.majorizes.trans (Majorizes.of_permuted ⟨σ, rfl⟩)

theorem majorizes_iff_balancing_then_permutation (x y : Fin n → ℝ) : Majorizes x y ↔
    ∃ z : Fin n → ℝ, BalancingChain x z ∧ ∃ σ : Equiv.Perm (Fin n), y = z ∘ σ := by
  constructor
  · intro h
    obtain ⟨σ, hc⟩ := h.exists_balancingChain_permuted
    refine ⟨y ∘ σ, hc, σ.symm, ?_⟩
    funext i
    simp
  · rintro ⟨z, hc, σ, hσ⟩
    exact hc.to_transferChain.majorizes.trans
      (MajorizationTransferStep.majorizes (Or.inr ⟨σ, hσ⟩))

end TimeTraps.Analysis
