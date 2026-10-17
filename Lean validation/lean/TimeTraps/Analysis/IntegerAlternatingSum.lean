module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! For finitely supported real data on the integers, the paired
alternating sum agrees with the even sum minus the odd sum. A cutoff
containing the support gives exact equality, not just convergence. -/

namespace TimeTraps.Analysis

open Set Filter Function
open scoped Topology

theorem integerAlternatingSum_parity (f : ℤ → ℝ) (hf : f.HasFiniteSupport) :
    (∑' j : ℤ, (j.negOnePow : ℝ) * f j) =
      (∑' k : ℤ, f (2 * k)) - ∑' k : ℤ, f (2 * k + 1) := by
  let g : ℤ → ℝ := fun j => (j.negOnePow : ℝ) * f j
  have hi : Injective (fun k : ℤ => 2 * k) := by
    intro i j h
    change 2 * i = 2 * j at h
    omega
  have hj : Injective (fun k : ℤ => 2 * k + 1) := by
    intro i j h
    change 2 * i + 1 = 2 * j + 1 at h
    omega
  have hs : Summable f := summable_of_hasFiniteSupport hf
  have he : HasSum (g ∘ (fun k : ℤ => 2 * k)) (∑' k : ℤ, f (2 * k)) := by
    simpa [g, Function.comp_def] using (hs.comp_injective hi).hasSum
  have ho : HasSum (g ∘ (fun k : ℤ => 2 * k + 1)) (-(∑' k : ℤ, f (2 * k + 1))) := by
    simpa [g, Function.comp_def] using (hs.comp_injective hj).hasSum.neg
  have hc : IsCompl (range (fun k : ℤ => 2 * k)) (range (fun k : ℤ => 2 * k + 1)) := by
    simpa only [range_two_mul, range_two_mul_add_one] using Int.isCompl_even_odd
  have hsum := HasSum.add_isCompl hc (hi.hasSum_range_iff.mpr he) (hj.hasSum_range_iff.mpr ho)
  simpa only [sub_eq_add_neg] using hsum.tsum_eq

theorem integerAlternatingSum_paired (f : ℤ → ℝ) (hf : f.HasFiniteSupport) :
    f 0 + (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * (f (n + 1) + f (-(n + 1)))) =
      (∑' k : ℤ, f (2 * k)) - ∑' k : ℤ, f (2 * k + 1) := by
  let g : ℤ → ℝ := fun j => (j.negOnePow : ℝ) * f j
  have hg : Summable g := summable_of_hasFiniteSupport
    (Function.HasFiniteSupport.mul_right (fun j : ℤ => (j.negOnePow : ℝ)) hf)
  have hp : Summable (fun n : ℕ => g (n + 1)) :=
    hg.comp_injective (fun i j h => by omega)
  have hn : Summable (fun n : ℕ => g (-(n + 1))) :=
    hg.comp_injective (fun i j h => by omega)
  have he (n : ℕ) : g (n + 1) + g (-(n + 1)) =
      (-1 : ℝ) ^ (n + 1) * (f (n + 1) + f (-(n + 1))) := by
    have hpw : ((n + 1 : ℤ).negOnePow : ℝ) = (-1 : ℝ) ^ (n + 1) := by
      exact_mod_cast Int.cast_negOnePow_natCast ℝ (n + 1)
    simp only [g, Int.negOnePow_neg, hpw, mul_add]
  have hid := tsum_of_add_one_of_neg_add_one hp hn
  have hpair : (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * (f (n + 1) + f (-(n + 1)))) =
      (∑' n : ℕ, g (n + 1)) + ∑' n : ℕ, g (-(n + 1)) := by
    rw [← hp.tsum_add hn]
    exact tsum_congr (fun n => (he n).symm)
  calc
    _ = ∑' j : ℤ, g j := by
      rw [hpair, hid]
      simp only [g, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul]
      ring
    _ = _ := integerAlternatingSum_parity f hf

theorem integerAlternatingSum_pair_eq_of_support (f : ℤ → ℝ) (J : Finset ℤ)
    (hz : ∀ j ∉ J, f j = 0) (N : ℕ) (hN : ∀ j ∈ J, j.natAbs ≤ N) :
    f 0 + (∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * (f (n + 1) + f (-(n + 1)))) =
      (∑' k : ℤ, f (2 * k)) - ∑' k : ℤ, f (2 * k + 1) := by
  have hf : f.HasFiniteSupport := J.finite_toSet.subset (fun j hj => by
    by_contra hn
    exact hj (hz j hn))
  have ht : ∀ n ∉ Finset.range N,
      (-1 : ℝ) ^ (n + 1) * (f (n + 1) + f (-(n + 1))) = 0 := by
    intro n hn
    have hge : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    have hpos : (n + 1 : ℤ) ∉ J := by
      intro hj
      have hh := hN _ hj
      have hh' : n + 1 ≤ N := by exact_mod_cast hh
      omega
    have hneg : (-(n + 1 : ℤ)) ∉ J := by
      intro hj
      have hh := hN _ hj
      rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl] at hh
      have hh' : n + 1 ≤ N := by
        simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hh
      omega
    rw [hz _ hpos, hz _ hneg, add_zero, mul_zero]
  have htSum : (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * (f (n + 1) + f (-(n + 1)))) =
      ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * (f (n + 1) + f (-(n + 1))) :=
    tsum_eq_sum (L := SummationFilter.unconditional ℕ) ht
  rw [← htSum]
  exact integerAlternatingSum_paired f hf

end TimeTraps.Analysis
