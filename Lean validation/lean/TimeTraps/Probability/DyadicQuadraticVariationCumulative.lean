module

public import TimeTraps.Probability.BrownianIntegralSquareGrid
public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariation

@[expose] public section

/-! The sum of completed-cell squared increments is monotone in time.
On the cell containing the stopping time, its difference from the actual
stopped quadratic variation is exactly one partial-cell square. -/

namespace TimeTraps.Probability

open Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def dyadicCumulativeQV (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) : ℝ :=
  ∑ i : Fin (2 ^ n), if brownianDyadicGrid T n i.succ ≤ s then
    (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) ^ 2 else 0

theorem dyadicCumulativeQV_nonneg (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) :
    0 ≤ dyadicCumulativeQV f T n s := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

theorem dyadicCumulativeQV_monotone (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    Monotone (dyadicCumulativeQV f T n) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro i _
  by_cases hs : brownianDyadicGrid T n i.succ ≤ s
  · simp only [if_pos hs, if_pos (hs.trans hst), le_refl]
  · simp only [if_neg hs]
    split_ifs <;> positivity

theorem dyadicCumulativeQV_zero (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicCumulativeQV f T n 0 = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : brownianDyadicGrid T n i.succ ≤ 0
  · have hr : brownianDyadicGrid T n i.succ = 0 := le_antisymm hi zero_le
    have hl : brownianDyadicGrid T n i.castSucc = 0 := le_antisymm
      ((brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)).trans hi) zero_le
    rw [if_pos hi]
    simp only [hr, hl, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · exact if_neg hi

theorem dyadicStoppedQV_sub_cumulative_cell (f : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ)
    (s : ℝ≥0) (i : Fin (2 ^ n))
    (hi : s.val ∈ Ioc (brownianDyadicGrid T n i.castSucc).val
      (brownianDyadicGrid T n i.succ).val) :
    finiteQuadraticVariation (fun j => f (min s (brownianDyadicGrid T n j))) -
      dyadicCumulativeQV f T n s =
      if brownianDyadicGrid T n i.succ ≤ s then 0 else
        (f s - f (brownianDyadicGrid T n i.castSucc)) ^ 2 := by
  classical
  rw [finiteQuadraticVariation, dyadicCumulativeQV, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single i]
  · by_cases hr : brownianDyadicGrid T n i.succ ≤ s
    · have hl := (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)).trans hr
      simp only [min_eq_right hr, min_eq_right hl, if_pos hr, sub_self]
    · simp only [min_eq_left (show s ≤ brownianDyadicGrid T n i.succ from hi.2),
        min_eq_right (show brownianDyadicGrid T n i.castSucc ≤ s from hi.1.le), if_neg hr, sub_zero]
  · intro j _ hji
    by_cases hr : brownianDyadicGrid T n j.succ ≤ s
    · have hl := (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ j)).trans hr
      simp only [min_eq_right hr, min_eq_right hl, if_pos hr, sub_self]
    · have hsright : s ≤ brownianDyadicGrid T n j.succ := (lt_of_not_ge hr).le
      have hsleft : s ≤ brownianDyadicGrid T n j.castSucc := by
        by_contra h
        exact hji (brownianDyadicGrid_cell_unique T n ⟨lt_of_not_ge h, hsright⟩ hi)
      simp only [min_eq_left hsright, min_eq_left hsleft, if_neg hr, sub_self,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · simp

end TimeTraps.Probability
