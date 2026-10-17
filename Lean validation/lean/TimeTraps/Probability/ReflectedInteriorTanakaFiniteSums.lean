module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeRegularity
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

/-! Finite paired integer sums stabilize uniformly in an auxiliary
parameter whenever the underlying integer family has uniform finite
support. This will be applied to actual local-time lattice corrections. -/

noncomputable section

namespace TimeTraps.Probability

open Set Filter
open scoped Topology

def integerPairedPartialSum (f : ℤ → ℝ) (N : ℕ) : ℝ :=
  f 0 + ∑ n ∈ Finset.range N, (f ((n + 1 : ℕ) : ℤ) + f (-((n + 1 : ℕ) : ℤ)))

def integerSplitPartialSum (f : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (f (n : ℤ) + f (-((n + 1 : ℕ) : ℤ)))

theorem integerPairedPartialSum_eq_tsum (f : ℤ → ℝ) (N : ℕ)
    (hp : ∀ n, N ≤ n → f ((n + 1 : ℕ) : ℤ) = 0)
    (hm : ∀ n, N ≤ n → f (-((n + 1 : ℕ) : ℤ)) = 0) :
    integerPairedPartialSum f N = ∑' k : ℤ, f k := by
  have hpos : HasSum (fun n : ℕ => f ((n + 1 : ℕ) : ℤ))
      (∑ n ∈ Finset.range N, f ((n + 1 : ℕ) : ℤ)) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => hp n (Nat.le_of_not_lt (Finset.mem_range.not.mp hn)))
  have hneg : HasSum (fun n : ℕ => f (-((n + 1 : ℕ) : ℤ)))
      (∑ n ∈ Finset.range N, f (-((n + 1 : ℕ) : ℤ))) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => hm n (Nat.le_of_not_lt (Finset.mem_range.not.mp hn)))
  have h : HasSum f ((∑ n ∈ Finset.range N, f ((n + 1 : ℕ) : ℤ)) + f 0 +
      ∑ n ∈ Finset.range N, f (-((n + 1 : ℕ) : ℤ))) := by
    apply HasSum.of_add_one_of_neg_add_one
    · simpa only [Nat.cast_add, Nat.cast_one] using hpos
    · simpa only [Nat.cast_add, Nat.cast_one] using hneg
  rw [h.tsum_eq, integerPairedPartialSum, Finset.sum_add_distrib]
  ring

theorem integerSplitPartialSum_eq_tsum (f : ℤ → ℝ) (N : ℕ)
    (hp : ∀ n, N ≤ n → f (n : ℤ) = 0)
    (hm : ∀ n, N ≤ n → f (-((n + 1 : ℕ) : ℤ)) = 0) :
    integerSplitPartialSum f N = ∑' k : ℤ, f k := by
  have h : HasSum (fun n : ℕ => f (n : ℤ) + f (-((n + 1 : ℕ) : ℤ)))
      (integerSplitPartialSum f N) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      have hn' : N ≤ n := Nat.le_of_not_lt (Finset.mem_range.not.mp hn)
      rw [hp n hn', hm n hn', add_zero])
  have hpos : HasSum (fun n : ℕ => f (n : ℤ))
      (∑ n ∈ Finset.range N, f (n : ℤ)) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => hp n (Nat.le_of_not_lt (Finset.mem_range.not.mp hn)))
  have hneg : HasSum (fun n : ℕ => f (-((n + 1 : ℕ) : ℤ)))
      (∑ n ∈ Finset.range N, f (-((n + 1 : ℕ) : ℤ))) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => hm n (Nat.le_of_not_lt (Finset.mem_range.not.mp hn)))
  have hall : HasSum f ((∑ n ∈ Finset.range N, f (n : ℤ)) +
      ∑ n ∈ Finset.range N, f (-((n + 1 : ℕ) : ℤ))) := by
    apply HasSum.of_nat_of_neg_add_one hpos
    simpa only [Nat.cast_add, Nat.cast_one] using hneg
  rw [hall.tsum_eq, integerSplitPartialSum, Finset.sum_add_distrib]

theorem integerPartialSums_eventually_eq {α : Type*} (F : ℤ → α → ℝ)
    (S : Set α) (J : Finset ℤ) (hF : ∀ k ∉ J, ∀ s ∈ S, F k s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ s ∈ S,
      integerPairedPartialSum (fun k => F k s) N = ∑' k : ℤ, F k s ∧
      integerSplitPartialSum (fun k => F k s) N = ∑' k : ℤ, F k s := by
  filter_upwards [eventually_ge_atTop (J.sup Int.natAbs + 1)] with N hN
  intro s hs
  have hz (k : ℤ) (hk : J.sup Int.natAbs < k.natAbs) : F k s = 0 :=
    hF k (fun hkJ => (not_le_of_gt hk) (Finset.le_sup hkJ)) s hs
  have hp (n : ℕ) (hn : N ≤ n) : F (n : ℤ) s = 0 :=
    hz n (by simpa only [Int.natAbs_natCast] using (show J.sup Int.natAbs < n by omega))
  have hps (n : ℕ) (hn : N ≤ n) : F ((n + 1 : ℕ) : ℤ) s = 0 := hp (n + 1) (by omega)
  have hm (n : ℕ) (hn : N ≤ n) : F (-((n + 1 : ℕ) : ℤ)) s = 0 :=
    hz _ (by simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
      (show J.sup Int.natAbs < n + 1 by omega))
  exact ⟨integerPairedPartialSum_eq_tsum _ N hps hm,
    integerSplitPartialSum_eq_tsum _ N hp hm⟩

end TimeTraps.Probability

end
