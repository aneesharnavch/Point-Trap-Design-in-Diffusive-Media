module

public import TimeTraps.Probability.DyadicQuadraticVariationApproximation

@[expose] public section

/-! Finite coarse-cell algebra for actual dyadic quadratic variation.
All weights multiply the actual nonnegative increment squares. Coarse
cell masses are differences of the completed-cell cumulative sum. -/

namespace TimeTraps.Probability

open Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def dyadicWeightedPathQV (f g : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i : Fin (2 ^ n), g (brownianDyadicGrid T n i.castSucc) *
    (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) ^ 2

noncomputable def dyadicCoarseWeight (g : ℝ≥0 → ℝ) (T : ℝ≥0) (m : ℕ) (s : ℝ≥0) : ℝ :=
  ∑ j : Fin (2 ^ m), if s ∈ Ioc (brownianDyadicGrid T m j.castSucc) (brownianDyadicGrid T m j.succ)
    then g (brownianDyadicGrid T m j.castSucc) else 0

noncomputable def dyadicCoarseWeightedQV (f g : ℝ≥0 → ℝ) (T : ℝ≥0) (m n : ℕ) : ℝ :=
  ∑ j : Fin (2 ^ m), g (brownianDyadicGrid T m j.castSucc) *
    (dyadicCumulativeQV f T n (brownianDyadicGrid T m j.succ) -
      dyadicCumulativeQV f T n (brownianDyadicGrid T m j.castSucc))

theorem dyadicCumulativeQV_interval (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ)
    {u v : ℝ≥0} (huv : u ≤ v) :
    dyadicCumulativeQV f T n v - dyadicCumulativeQV f T n u =
      ∑ i : Fin (2 ^ n), if brownianDyadicGrid T n i.succ ∈ Ioc u v then
        (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) ^ 2 else 0 := by
  classical
  rw [dyadicCumulativeQV, dyadicCumulativeQV, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hu : brownianDyadicGrid T n i.succ ≤ u
  · have hv := hu.trans huv
    simp only [if_pos hu, if_pos hv, mem_Ioc, not_lt_of_ge hu, false_and, if_false, sub_self]
  · have hut : u < brownianDyadicGrid T n i.succ := lt_of_not_ge hu
    by_cases hv : brownianDyadicGrid T n i.succ ≤ v <;>
      simp only [if_neg hu, mem_Ioc, hut, true_and, hv, ite_true, ite_false, sub_zero]

theorem dyadicCoarseWeight_cell (g : ℝ≥0 → ℝ) (T : ℝ≥0) (m : ℕ)
    (s : ℝ≥0) (j : Fin (2 ^ m))
    (hj : s ∈ Ioc (brownianDyadicGrid T m j.castSucc) (brownianDyadicGrid T m j.succ)) :
    dyadicCoarseWeight g T m s = g (brownianDyadicGrid T m j.castSucc) := by
  classical
  rw [dyadicCoarseWeight, Finset.sum_eq_single j]
  · exact if_pos hj
  · intro k _ hkj
    have hk : s ∉ Ioc (brownianDyadicGrid T m k.castSucc) (brownianDyadicGrid T m k.succ) := by
      intro hk
      exact hkj (brownianDyadicGrid_cell_unique T m (r := s.val) hk hj)
    exact if_neg hk
  · simp

theorem dyadicCoarseWeightedQV_eq (f g : ℝ≥0 → ℝ) (T : ℝ≥0) (m n : ℕ) :
    dyadicCoarseWeightedQV f g T m n =
      ∑ i : Fin (2 ^ n), dyadicCoarseWeight g T m (brownianDyadicGrid T n i.succ) *
        (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) ^ 2 := by
  classical
  unfold dyadicCoarseWeightedQV
  simp_rw [dyadicCumulativeQV_interval f T n (brownianDyadicGrid_monotone T m (Fin.castSucc_le_succ _)),
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [dyadicCoarseWeight, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : brownianDyadicGrid T n i.succ ∈
      Ioc (brownianDyadicGrid T m j.castSucc) (brownianDyadicGrid T m j.succ)
  · simp only [if_pos hj]
  · simp only [if_neg hj, mul_zero, zero_mul]

theorem dyadicWeightedPathQV_coarse_error (f g : ℝ≥0 → ℝ) (T : ℝ≥0) (m n : ℕ)
    {η : ℝ} (hη : ∀ i : Fin (2 ^ n),
      |g (brownianDyadicGrid T n i.castSucc) -
        dyadicCoarseWeight g T m (brownianDyadicGrid T n i.succ)| ≤ η) :
    |dyadicWeightedPathQV f g T n - dyadicCoarseWeightedQV f g T m n| ≤ η * dyadicPathQV f T n := by
  rw [dyadicWeightedPathQV, dyadicCoarseWeightedQV_eq, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin (2 ^ n), |g (brownianDyadicGrid T n i.castSucc) *
        (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) ^ 2 -
        dyadicCoarseWeight g T m (brownianDyadicGrid T n i.succ) *
        (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (2 ^ n), η *
        (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_mul, abs_mul, abs_sq]
      exact mul_le_mul_of_nonneg_right (hη i) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem stoppedDyadicPathQV_terminal (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    stoppedDyadicPathQV f T n T = dyadicPathQV f T n := by
  unfold stoppedDyadicPathQV dyadicPathQV
  congr 1
  funext i
  rw [min_eq_right (brownianDyadicGrid_mem_Icc T n i).2]

theorem dyadicWeightedPathQV_zero (f g : ℝ≥0 → ℝ) (n : ℕ) :
    dyadicWeightedPathQV f g 0 n = 0 := by
  simp [dyadicWeightedPathQV, brownianDyadicGrid]

end TimeTraps.Probability
