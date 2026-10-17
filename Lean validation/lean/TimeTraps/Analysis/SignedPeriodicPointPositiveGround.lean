module

public import TimeTraps.Analysis.SignedPeriodicPointPositiveGroundRegularity
public import TimeTraps.Analysis.SignedPeriodicPointPositiveGroundSeam

@[expose] public section

/-! Every nonzero nonnegative periodic weak eigenstate is strictly
positive throughout the closed interval, including the seam. Real contact
strengths and real eigenvalues of either sign are allowed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.nonnegative_eigenstate_pos
    (P : SignedPeriodicPointProblem ι l r) (u : IntervalPeriodicSpace P.boundary) (ev : ℝ)
    (hu : u ≠ 0)
    (hnonneg : ∀ x ∈ Icc l r, 0 ≤ u.val.representative P.boundary.interval_pos x)
    (he : ∀ v : IntervalPeriodicSpace P.boundary,
      P.form u v = ev * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v)) :
    ∀ x ∈ Icc l r, 0 < u.val.representative P.boundary.interval_pos x := by
  obtain ⟨n, Q, j, hj, ht⟩ := P.eigen_linear_piecewise u ev he
  intro x hx
  by_contra hn
  have hz : u.val.representative P.boundary.interval_pos x = 0 :=
    le_antisymm (le_of_not_gt hn) (hnonneg x hx)
  have hzero := Q.eq_zero_of_nonnegative_zero hj ht hnonneg hx hz
  apply hu
  apply P.boundary.stateL_injective
  rw [map_zero]
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo l r))).symm
  filter_upwards [(u.val.representative_spec P.boundary.interval_pos).2.1,
    ae_restrict_mem measurableSet_Ioo] with y hy hmem
  exact hy.trans (hzero y (Ioo_subset_Icc_self hmem))

end TimeTraps.Analysis
