module

public import TimeTraps.Analysis.DirichletPositiveGround

@[expose] public section

/-! The first Dirichlet/mixed eigenspace is determined by its value at
any interior point. Endpoint values are not used for normalization,
because the selected absorbing endpoint traces vanish. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem DirichletPointProblem.first_hilbert_zero_of_interior_zero
    (P : DirichletPointProblem ι l r) (u : IntervalDirichletSpace P.boundary)
    (he : ∀ v : IntervalDirichletSpace P.boundary,
      P.form u v = P.firstEigenvalue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v))
    {x : ℝ} (hx : x ∈ Ioo l r) (hz : u.val.representative P.boundary.interval_pos x = 0) : u = 0 := by
  by_contra hu
  have ha : P.boundary.absState u ≠ 0 := by
    intro hzero
    have hm := P.boundary.absState_mass u
    rw [hzero, map_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hm
    have hs : P.boundary.stateL u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hm.symm)
    apply hu
    apply P.boundary.stateL_injective
    simpa only [map_zero] using hs
  have heq : P.form (P.boundary.absState u) (P.boundary.absState u) =
      P.firstEigenvalue * ‖P.boundary.stateL (P.boundary.absState u)‖ ^ 2 := by
    rw [P.absState_form, P.boundary.absState_mass, he u, real_inner_self_eq_norm_sq]
  have hnonneg : ∀ y ∈ Icc l r,
      0 ≤ (P.boundary.absState u).val.representative P.boundary.interval_pos y := by
    intro y hy
    rw [P.boundary.absState_representative u hy]
    exact abs_nonneg _
  have hp := P.nonnegative_eigenstate_pos (P.boundary.absState u) P.firstEigenvalue ha hnonneg
    (P.first_minimizer_hilbert _ heq) x hx
  rw [P.boundary.absState_representative u (Ioo_subset_Icc_self hx)] at hp
  change 0 < |u.val.representative P.boundary.interval_pos x| at hp
  rw [hz, abs_zero] at hp
  exact lt_irrefl 0 hp

theorem DirichletPointProblem.first_hilbert_scalar
    (P : DirichletPointProblem ι l r) (u v : IntervalDirichletSpace P.boundary)
    {x : ℝ} (hx : x ∈ Ioo l r) (hu₀ : u.val.representative P.boundary.interval_pos x ≠ 0)
    (hu : ∀ w : IntervalDirichletSpace P.boundary,
      P.form u w = P.firstEigenvalue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL w))
    (hv : ∀ w : IntervalDirichletSpace P.boundary,
      P.form v w = P.firstEigenvalue * inner ℝ (P.boundary.stateL v) (P.boundary.stateL w)) :
    v = (v.val.representative P.boundary.interval_pos x /
      u.val.representative P.boundary.interval_pos x) • u := by
  let c := v.val.representative P.boundary.interval_pos x / u.val.representative P.boundary.interval_pos x
  have he : ∀ w : IntervalDirichletSpace P.boundary,
      P.form (v - c • u) w = P.firstEigenvalue *
        inner ℝ (P.boundary.stateL (v - c • u)) (P.boundary.stateL w) := by
    intro w
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
      inner_sub_left, real_inner_smul_left, hu, hv]
    ring
  have hz : (v - c • u).val.representative P.boundary.interval_pos x = 0 := by
    change evalL P.boundary.interval_pos x (Ioo_subset_Icc_self hx) (v.val - c • u.val) = 0
    simp only [map_sub, map_smul, smul_eq_mul]
    change v.val.representative P.boundary.interval_pos x -
      c * u.val.representative P.boundary.interval_pos x = 0
    dsimp only [c]
    rw [div_mul_cancel₀ _ hu₀, sub_self]
  exact sub_eq_zero.mp (P.first_hilbert_zero_of_interior_zero (v - c • u) he hx hz)

end TimeTraps.Analysis
