module

public import TimeTraps.Probability.BrownianIntegralFourthPartialSum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-! Deterministic finite energy and the polynomial estimate converting
the exact Gaussian fourth recursion into a running-maximum pairing. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*}

def brownianFourthEnergy (τ : ℕ → ℝ≥0) (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, ((τ (i + 1)).val - (τ i).val) * ξ i ω ^ 2

theorem brownianFourthEnergy_nonneg (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ brownianFourthEnergy τ ξ n ω :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hτ (Nat.le_succ i))) (sq_nonneg _))

theorem brownian_fourth_energy_path_bound (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (M ξ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n, (6 * ((τ (i + 1)).val - (τ i).val) *
      (M i ω ^ 2 * ξ i ω ^ 2) + 3 * ((τ (i + 1)).val - (τ i).val) ^ 2 * ξ i ω ^ 4)) ≤
      6 * ((finiteRunningMax (fun i => |M i ω|) n) ^ 2 * brownianFourthEnergy τ ξ n ω) +
        3 * brownianFourthEnergy τ ξ n ω ^ 2 := by
  let R := finiteRunningMax (fun i => |M i ω|) n
  have hR : 0 ≤ R := finiteRunningMax_nonneg _ (abs_nonneg _) n
  have hi (i : ℕ) (hi : i ∈ Finset.range n) : M i ω ^ 2 ≤ R ^ 2 := by
    have hm := le_finiteRunningMax (fun k => |M k ω|) (Nat.le_of_lt (Finset.mem_range.mp hi))
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr hm
  have hmain : (∑ i ∈ Finset.range n, 6 * ((τ (i + 1)).val - (τ i).val) * (M i ω ^ 2 * ξ i ω ^ 2)) ≤
      6 * (R ^ 2 * brownianFourthEnergy τ ξ n ω) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, 6 * (R ^ 2 * (((τ (i + 1)).val - (τ i).val) * ξ i ω ^ 2)) := by
        apply Finset.sum_le_sum
        intro i hi'
        have hδ : 0 ≤ (τ (i + 1)).val - (τ i).val := sub_nonneg.mpr (hτ (Nat.le_succ i))
        have hb := mul_le_mul_of_nonneg_right (hi i hi') (mul_nonneg hδ (sq_nonneg (ξ i ω)))
        nlinarith
      _ = _ := by simp only [brownianFourthEnergy, Finset.mul_sum]
  have hdiag : (∑ i ∈ Finset.range n, 3 * ((τ (i + 1)).val - (τ i).val) ^ 2 * ξ i ω ^ 4) ≤
      3 * brownianFourthEnergy τ ξ n ω ^ 2 := by
    have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.range n)
      (f := fun i => ((τ (i + 1)).val - (τ i).val) * ξ i ω ^ 2)
      (fun i _ => mul_nonneg (sub_nonneg.mpr (hτ (Nat.le_succ i))) (sq_nonneg _))
    have he : (∑ i ∈ Finset.range n, 3 * ((τ (i + 1)).val - (τ i).val) ^ 2 * ξ i ω ^ 4) =
        3 * ∑ i ∈ Finset.range n, (((τ (i + 1)).val - (τ i).val) * ξ i ω ^ 2) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hs (by norm_num)
  rw [Finset.sum_add_distrib]
  exact add_le_add hmain hdiag

theorem brownian_fourth_energy_scalar_bound {q c e : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hpair : q ≤ 6 * c + 3 * e) (hcs : c ^ 2 ≤ 4 * q * e) : q ≤ 150 * e := by
  have hY : 6 * c ≤ q / 2 + 72 * e := by
    have hs : (6 * c) ^ 2 ≤ (q / 2 + 72 * e) ^ 2 := by
      nlinarith [sq_nonneg (q / 2 - 72 * e)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  linarith

end TimeTraps.Probability
