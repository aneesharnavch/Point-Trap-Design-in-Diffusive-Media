module

public import TimeTraps.Analysis.RegularSturmPositiveGroundRegularity
public import TimeTraps.Analysis.RegularSturmPositiveGroundZeros

@[expose] public section

/-! Every nonzero nonnegative weak eigenstate of the actual regular variable-coefficient
Sturm operator is strictly positive on the open interval.
The eigenvalue and point strengths may have either sign; selected
absorbing endpoint zeros remain allowed. No spectral premise is used. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.nonnegative_eigenstate_pos
    (P : RegularSturmProblem ι l r) (u : IntervalSeparatedSpace P.boundary) (ev : ℝ)
    (hu : u ≠ 0)
    (hnonneg : ∀ x ∈ Icc l r, 0 ≤ u.val.representative P.boundary.interval_pos x)
    (he : ∀ v : IntervalSeparatedSpace P.boundary,
      P.form u v = ev * inner ℝ (P.stateL u) (P.stateL v)) :
    ∀ x ∈ Ioo l r, 0 < u.val.representative P.boundary.interval_pos x := by
  obtain ⟨n, Q, j, hj, ht⟩ := P.eigen_linear_piecewise u ev he
  intro x hx
  by_contra hn
  have hz : u.val.representative P.boundary.interval_pos x = 0 :=
    le_antisymm (le_of_not_gt hn) (hnonneg x (Ioo_subset_Icc_self hx))
  have hzero := Q.eq_zero_of_nonnegative_interior_zero
    (P.potential_continuous.sub (continuousOn_const.mul P.speed_continuous)) hj ht hnonneg hx hz
  apply hu
  apply P.boundary.stateL_injective
  rw [map_zero]
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo l r))).symm
  filter_upwards [(u.val.representative_spec P.boundary.interval_pos).2.1,
    ae_restrict_mem measurableSet_Ioo] with y hy hmem
  exact hy.trans (hzero y (Ioo_subset_Icc_self hmem))

end TimeTraps.Analysis
