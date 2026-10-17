module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Exact finite Euclidean square estimates used to combine two independent
position-error bounds. -/

namespace TimeTraps.Analysis

open scoped BigOperators

variable {ι : Type*}

theorem finite_sum_add_sq_le (s : Finset ι) (e h : ι → ℝ) :
    (∑ i ∈ s, (e i + h i) ^ 2) ≤
      (Real.sqrt (∑ i ∈ s, e i ^ 2) + Real.sqrt (∑ i ∈ s, h i ^ 2)) ^ 2 := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt s e h
  have he := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (e i)) :
    0 ≤ ∑ i ∈ s, e i ^ 2)
  have hh := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (h i)) :
    0 ≤ ∑ i ∈ s, h i ^ 2)
  have hid : (∑ i ∈ s, (e i + h i) ^ 2) =
      (∑ i ∈ s, e i ^ 2) + 2 * (∑ i ∈ s, e i * h i) + ∑ i ∈ s, h i ^ 2 := by
    simp_rw [show ∀ i, (e i + h i) ^ 2 = e i ^ 2 + 2 * (e i * h i) + h i ^ 2 by
      intro i; ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith

theorem finite_sum_add_sq_control (s : Finset ι) (e h : ι → ℝ) {B N C : ℝ}
    (hB : 0 ≤ B) (hN : 0 ≤ N)
    (he : (∑ i ∈ s, e i ^ 2) ≤ B * N ^ 2)
    (hh : (∑ i ∈ s, h i ^ 2) ≤ B * C) :
    (∑ i ∈ s, (e i + h i) ^ 2) ≤ B * (N + Real.sqrt C) ^ 2 := by
  have hr1 : Real.sqrt (∑ i ∈ s, e i ^ 2) ≤ Real.sqrt B * N := by
    have ht := Real.sqrt_le_sqrt he
    rwa [Real.sqrt_mul hB, Real.sqrt_sq hN] at ht
  have hr2 : Real.sqrt (∑ i ∈ s, h i ^ 2) ≤ Real.sqrt B * Real.sqrt C := by
    have ht := Real.sqrt_le_sqrt hh
    rwa [Real.sqrt_mul hB] at ht
  have hr := add_le_add hr1 hr2
  have hsq : (Real.sqrt (∑ i ∈ s, e i ^ 2) + Real.sqrt (∑ i ∈ s, h i ^ 2)) ^ 2 ≤
      (Real.sqrt B * N + Real.sqrt B * Real.sqrt C) ^ 2 :=
    (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (add_nonneg (mul_nonneg (Real.sqrt_nonneg B) hN)
        (mul_nonneg (Real.sqrt_nonneg B) (Real.sqrt_nonneg C)))).mpr hr
  have hb := (finite_sum_add_sq_le s e h).trans hsq
  have heq : (Real.sqrt B * N + Real.sqrt B * Real.sqrt C) ^ 2 =
      B * (N + Real.sqrt C) ^ 2 := by
    rw [← mul_add, mul_pow, Real.sq_sqrt hB]
  rwa [heq] at hb

end TimeTraps.Analysis
