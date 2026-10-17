module

public import TimeTraps.Analysis.FinitePrefix
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-! Majorization in its usual decreasing-sort, partial-sum formulation.
Sorting is a proved permutation of the given vector, including repeated entries. -/

namespace TimeTraps.Analysis

open scoped BigOperators

variable {n : ℕ}

noncomputable def descendingOrder (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => OrderDual.toDual (x i))

noncomputable def descending (x : Fin n → ℝ) (i : Fin n) : ℝ := x (descendingOrder x i)

theorem descending_antitone (x : Fin n → ℝ) : Antitone (descending x) :=
  Tuple.monotone_sort (fun i => OrderDual.toDual (x i))

theorem descending_map_sum (f : ℝ → ℝ) (x : Fin n → ℝ) :
    (∑ i, f (descending x i)) = ∑ i, f (x i) :=
  Equiv.sum_comp (descendingOrder x) (fun i => f (x i))

theorem descending_sum (x : Fin n → ℝ) : (∑ i, descending x i) = ∑ i, x i :=
  descending_map_sum id x

theorem descending_eq_iff_permuted (x y : Fin n → ℝ) :
    descending x = descending y ↔ ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  constructor
  · intro he
    refine ⟨(descendingOrder x).symm.trans (descendingOrder y), ?_⟩
    funext i
    have h := congrFun he ((descendingOrder x).symm i)
    simpa [descending] using h
  · rintro ⟨σ, rfl⟩
    exact Tuple.comp_perm_comp_sort_eq_comp_sort
      (f := fun i => OrderDual.toDual (y i)) (σ := σ)

structure Majorizes (x y : Fin n → ℝ) : Prop where
  total : (∑ i, x i) = ∑ i, y i
  prefix_interior : ∀ k, 0 < k → k < n → vectorPrefix (descending y) k ≤ vectorPrefix (descending x) k

theorem Majorizes.prefix_le {x y : Fin n → ℝ} (h : Majorizes x y) (k : ℕ) (hk : k ≤ n) :
    vectorPrefix (descending y) k ≤ vectorPrefix (descending x) k := by
  by_cases hz : k = 0
  · subst k
    rw [vectorPrefix_zero, vectorPrefix_zero]
  · by_cases hn : k = n
    · subst k
      rw [vectorPrefix_total, vectorPrefix_total, descending_sum, descending_sum, h.total]
    · exact h.prefix_interior k (Nat.pos_of_ne_zero hz) (lt_of_le_of_ne hk hn)

theorem Majorizes.refl (x : Fin n → ℝ) : Majorizes x x :=
  ⟨rfl, fun _ _ _ => le_rfl⟩

theorem Majorizes.trans {x y z : Fin n → ℝ} (hxy : Majorizes x y) (hyz : Majorizes y z) :
    Majorizes x z :=
  ⟨hxy.total.trans hyz.total,
    fun k hk hkn => (hyz.prefix_interior k hk hkn).trans (hxy.prefix_interior k hk hkn)⟩

theorem Majorizes.of_permuted {x y : Fin n → ℝ}
    (h : ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ) : Majorizes x y := by
  have hs := (descending_eq_iff_permuted x y).mpr h
  constructor
  · have ht := congrArg (fun z : Fin n → ℝ => ∑ i, z i) hs
    simpa only [descending_sum] using ht
  · intro k _ _
    rw [hs]

theorem Majorizes.antisymm_permuted {x y : Fin n → ℝ}
    (hxy : Majorizes x y) (hyx : Majorizes y x) :
    ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  apply (descending_eq_iff_permuted x y).mp
  funext i
  have h₀ : vectorPrefix (descending x) i.val = vectorPrefix (descending y) i.val :=
    le_antisymm (hyx.prefix_le i.val i.isLt.le) (hxy.prefix_le i.val i.isLt.le)
  have h₁ : vectorPrefix (descending x) (i.val + 1) = vectorPrefix (descending y) (i.val + 1) :=
    le_antisymm (hyx.prefix_le _ (Nat.succ_le_of_lt i.isLt))
      (hxy.prefix_le _ (Nat.succ_le_of_lt i.isLt))
  rw [vectorPrefix_succ, vectorPrefix_succ, h₀] at h₁
  linarith

end TimeTraps.Analysis
