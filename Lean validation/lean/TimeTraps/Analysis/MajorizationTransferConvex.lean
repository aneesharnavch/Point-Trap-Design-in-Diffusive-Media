module

public import TimeTraps.Analysis.MajorizationTransfer
public import TimeTraps.Analysis.Karamata

@[expose] public section

/-! Convex sums recover the standard sorted-prefix order through positive-part
test functions. In particular, every elementary balancing transfer preserves
majorization. -/

namespace TimeTraps.Analysis

open Set
open scoped BigOperators

variable {n : ℕ}

theorem vectorPrefix_sub_const_le_positivePart (x : Fin n → ℝ) (a : ℝ) (k : ℕ) :
    vectorPrefix x k - vectorPrefix (fun _ : Fin n => a) k ≤ ∑ i, max (x i - a) 0 := by
  rw [← vectorPrefix_sub]
  unfold vectorPrefix
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem positivePart_sum_eq_prefix (x : Fin n → ℝ) (hx : Antitone x) (k : Fin n) :
    (∑ i, max (x i - x k) 0) =
      vectorPrefix x k.val - vectorPrefix (fun _ : Fin n => x k) k.val := by
  rw [← vectorPrefix_sub]
  unfold vectorPrefix
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k.val
  · rw [if_pos hi, max_eq_left (sub_nonneg.mpr (hx (le_of_lt hi)))]
  · rw [if_neg hi, max_eq_right (sub_nonpos.mpr (hx (le_of_not_gt hi)))]

theorem Majorizes.of_convex_sums {x y : Fin n → ℝ}
    (htotal : (∑ i, x i) = ∑ i, y i)
    (hc : ∀ f : ℝ → ℝ, ConvexOn ℝ univ f → (∑ i, f (y i)) ≤ ∑ i, f (x i)) :
    Majorizes x y := by
  refine ⟨htotal, ?_⟩
  intro k _ hkn
  let a := descending x ⟨k, hkn⟩
  have hf : ConvexOn ℝ univ (fun t : ℝ => max (t - a) 0) :=
    ((convexOn_id convex_univ).sub (concaveOn_const a convex_univ)).sup
      (convexOn_const 0 convex_univ)
  have hs : (∑ i, max (descending y i - a) 0) ≤ ∑ i, max (descending x i - a) 0 := by
    rw [descending_map_sum (fun t => max (t - a) 0) y,
      descending_map_sum (fun t => max (t - a) 0) x]
    exact hc (fun t => max (t - a) 0) hf
  have hy := vectorPrefix_sub_const_le_positivePart (descending y) a k
  have hx := positivePart_sum_eq_prefix (descending x) (descending_antitone x) ⟨k, hkn⟩
  change (∑ i, max (descending x i - a) 0) =
    vectorPrefix (descending x) k - vectorPrefix (fun _ : Fin n => a) k at hx
  linarith

theorem majorizes_iff_convex_sums (x y : Fin n → ℝ) : Majorizes x y ↔
    (∑ i, x i) = ∑ i, y i ∧
      ∀ f : ℝ → ℝ, ConvexOn ℝ univ f → (∑ i, f (y i)) ≤ ∑ i, f (x i) := by
  constructor
  · intro h
    exact ⟨h.total, fun _ hf => h.convex_sum_le hf (fun _ => mem_univ _) (fun _ => mem_univ _)⟩
  · exact fun h => Majorizes.of_convex_sums h.1 h.2

theorem convex_balancing_pair_le {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f)
    {a b ε : ℝ} (hε : 0 < ε) (hbal : 2 * ε ≤ a - b) :
    f (a - ε) + f (b + ε) ≤ f a + f b := by
  have hab : 0 < a - b := by linarith
  let t := ε / (a - b)
  have ht : 0 ≤ t := div_nonneg hε.le hab.le
  have ht1 : t ≤ 1 := (div_le_one hab).mpr (by linarith)
  have hmul : t * (a - b) = ε := div_mul_cancel₀ ε hab.ne'
  have he₁ : (1 - t) * a + t * b = a - ε := by nlinarith
  have he₂ : t * a + (1 - t) * b = b + ε := by nlinarith
  have h₁ := hf.2 (mem_univ a) (mem_univ b) (sub_nonneg.mpr ht1) ht
    (show (1 - t) + t = 1 by ring)
  have h₂ := hf.2 (mem_univ a) (mem_univ b) ht (sub_nonneg.mpr ht1)
    (show t + (1 - t) = 1 by ring)
  simp only [smul_eq_mul, he₁, he₂] at h₁ h₂
  nlinarith

theorem balance_map_sum (f : ℝ → ℝ) (x : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) (ε : ℝ) :
    (∑ k, f (balance x i j ε k)) =
      (∑ k, f (x k)) - f (x i) - f (x j) + f (x i - ε) + f (x j + ε) := by
  classical
  have he (k : Fin n) : f (balance x i j ε k) = f (x k) +
      (if k = i then f (x i - ε) - f (x i) else 0) +
      (if k = j then f (x j + ε) - f (x j) else 0) := by
    by_cases hki : k = i
    · subst k
      simp [balance_donor x hij, hij]
    by_cases hkj : k = j
    · subst k
      simp [balance_receiver x hij, hij.symm]
    simp [balance_other x hki hkj, hki, hkj]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  ring

theorem BalancingStep.majorizes {x z : Fin n → ℝ} (h : BalancingStep x z) : Majorizes x z := by
  obtain ⟨i, j, ε, hij, hε, hbal, rfl⟩ := h
  apply Majorizes.of_convex_sums (balance_sum x i j ε).symm
  intro f hf
  rw [balance_map_sum f x hij]
  have hs := convex_balancing_pair_le hf hε hbal
  linarith

end TimeTraps.Analysis
