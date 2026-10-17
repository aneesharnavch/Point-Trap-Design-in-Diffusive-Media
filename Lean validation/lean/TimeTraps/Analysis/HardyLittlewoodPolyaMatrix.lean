module

public import TimeTraps.Analysis.HardyLittlewoodPolya
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.Convex.Jensen

@[expose] public section

/-! The doubly-stochastic formulation of finite majorization. The forward
matrix is a finite product of actual balancing and permutation matrices;
the reverse follows from Jensen's inequality and the convex-sum criterion. -/

namespace TimeTraps.Analysis

open Set Matrix
open scoped BigOperators

variable {n : ℕ}

theorem BalancingStep.exists_doublyStochastic {x y : Fin n → ℝ} (h : BalancingStep x y) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, M ∈ doublyStochastic ℝ (Fin n) ∧ y = M *ᵥ x := by
  obtain ⟨i, j, ε, hij, hε, hbal, rfl⟩ := h
  have hab : 0 < x i - x j := by linarith
  let t := ε / (x i - x j)
  have ht : 0 ≤ t := div_nonneg hε.le hab.le
  have ht1 : t ≤ 1 := (div_le_one hab).mpr (by linarith)
  have hmul : t * (x i - x j) = ε := div_mul_cancel₀ ε hab.ne'
  let M : Matrix (Fin n) (Fin n) ℝ :=
    (1 - t) • 1 + t • (Equiv.swap i j).permMatrix ℝ
  have hM : M ∈ doublyStochastic ℝ (Fin n) :=
    convex_doublyStochastic (doublyStochastic ℝ (Fin n)).one_mem
      permMatrix_mem_doublyStochastic (sub_nonneg.mpr ht1) ht (by ring)
  refine ⟨M, hM, ?_⟩
  dsimp only [M]
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, permMatrix_mulVec]
  funext k
  change balance x i j ε k = (1 - t) * x k + t * x (Equiv.swap i j k)
  by_cases hki : k = i
  · subst k
    rw [balance_donor x hij, Equiv.swap_apply_left]
    nlinarith
  by_cases hkj : k = j
  · subst k
    rw [balance_receiver x hij, Equiv.swap_apply_right]
    nlinarith
  rw [balance_other x hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
  ring

theorem MajorizationTransferStep.exists_doublyStochastic {x y : Fin n → ℝ}
    (h : MajorizationTransferStep x y) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, M ∈ doublyStochastic ℝ (Fin n) ∧ y = M *ᵥ x := by
  rcases h with hbal | ⟨σ, rfl⟩
  · exact hbal.exists_doublyStochastic
  · exact ⟨σ.permMatrix ℝ, permMatrix_mem_doublyStochastic, (permMatrix_mulVec σ).symm⟩

theorem MajorizationTransferChain.exists_doublyStochastic {x y : Fin n → ℝ}
    (h : MajorizationTransferChain x y) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, M ∈ doublyStochastic ℝ (Fin n) ∧ y = M *ᵥ x := by
  induction h with
  | refl => exact ⟨1, (doublyStochastic ℝ (Fin n)).one_mem, (one_mulVec _).symm⟩
  | tail _ hstep ih =>
    obtain ⟨M, hM, hMx⟩ := ih
    obtain ⟨N, hN, hNy⟩ := hstep.exists_doublyStochastic
    refine ⟨N * M, (doublyStochastic ℝ (Fin n)).mul_mem hN hM, ?_⟩
    rw [hNy, hMx, mulVec_mulVec]

theorem majorizes_mulVec_of_doublyStochastic {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ doublyStochastic ℝ (Fin n)) (x : Fin n → ℝ) : Majorizes x (M *ᵥ x) := by
  apply Majorizes.of_convex_sums (sum_mulVec_of_mem_doublyStochastic hM).symm
  intro f hf
  have hrow (i : Fin n) : f ((M *ᵥ x) i) ≤ ∑ j, M i j * f (x j) := by
    have hs := hf.map_sum_le (t := Finset.univ) (w := fun j => M i j) (p := x)
      (fun _ _ => nonneg_of_mem_doublyStochastic hM)
      (sum_row_of_mem_doublyStochastic hM i) (fun _ _ => mem_univ _)
    simpa only [mulVec, dotProduct, smul_eq_mul] using hs
  calc
    (∑ i, f ((M *ᵥ x) i)) ≤ ∑ i, ∑ j, M i j * f (x j) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = ∑ j, (∑ i, M i j) * f (x j) := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ = ∑ j, f (x j) := by simp only [sum_col_of_mem_doublyStochastic hM, one_mul]

theorem majorizes_iff_exists_doublyStochastic (x y : Fin n → ℝ) : Majorizes x y ↔
    ∃ M : Matrix (Fin n) (Fin n) ℝ, M ∈ doublyStochastic ℝ (Fin n) ∧ y = M *ᵥ x := by
  constructor
  · exact fun h => h.transferChain.exists_doublyStochastic
  · rintro ⟨M, hM, rfl⟩
    exact majorizes_mulVec_of_doublyStochastic hM x

end TimeTraps.Analysis
