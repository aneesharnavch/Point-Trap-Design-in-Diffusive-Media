module

public import TimeTraps.Analysis.DirichletPositiveGroundAbsolute
public import TimeTraps.Analysis.DirichletPositiveGroundRegularity
public import TimeTraps.Analysis.DirichletPositiveGroundZeros

@[expose] public section

/-! A nonzero nonnegative Dirichlet/mixed weak eigenstate is strictly
positive on the open interval. In particular the first actual eigenvalue
has a positive normalized ground state. Selected endpoint zeros remain;
the existing model retains nonnegative contact strengths. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem DirichletPointProblem.nonnegative_eigenstate_pos
    (P : DirichletPointProblem ι l r) (u : IntervalDirichletSpace P.boundary) (ev : ℝ)
    (hu : u ≠ 0)
    (hnonneg : ∀ x ∈ Icc l r, 0 ≤ u.val.representative P.boundary.interval_pos x)
    (he : ∀ v : IntervalDirichletSpace P.boundary,
      P.form u v = ev * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v)) :
    ∀ x ∈ Ioo l r, 0 < u.val.representative P.boundary.interval_pos x := by
  obtain ⟨n, Q, j, hj, ht⟩ := P.eigen_linear_piecewise u ev he
  intro x hx
  by_contra hn
  have hz : u.val.representative P.boundary.interval_pos x = 0 :=
    le_antisymm (le_of_not_gt hn) (hnonneg x (Ioo_subset_Icc_self hx))
  have hzero := Q.eq_zero_of_nonnegative_interior_zero hj ht hnonneg hx hz
  apply hu
  apply P.boundary.stateL_injective
  rw [map_zero]
  apply Lp.ext
  apply EventuallyEq.trans _ (Lp.coeFn_zero ℝ 2 (volume.restrict (Ioo l r))).symm
  filter_upwards [(u.val.representative_spec P.boundary.interval_pos).2.1,
    ae_restrict_mem measurableSet_Ioo] with y hy hmem
  exact hy.trans (hzero y (Ioo_subset_Icc_self hmem))

theorem DirichletPointProblem.positive_first_eigenstate (P : DirichletPointProblem ι l r) :
    ∃ u : IntervalDirichletSpace P.boundary,
      (∀ x ∈ Ioo l r, 0 < u.val.representative P.boundary.interval_pos x) ∧
      ‖P.boundary.stateL u‖ ^ 2 = 1 ∧
      ∀ v : IntervalDirichletSpace P.boundary,
        P.form u v = P.firstEigenvalue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v) := by
  obtain ⟨u, hnonneg, hnorm, he⟩ := P.nonnegative_first_eigenstate
  have hu : u ≠ 0 := by
    intro hz
    have hz' : (0 : ℝ) = 1 := by
      simpa only [hz, map_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hnorm
    exact zero_ne_one hz'
  exact ⟨u, P.nonnegative_eigenstate_pos u P.firstEigenvalue hu hnonneg he, hnorm, he⟩

end TimeTraps.Analysis
