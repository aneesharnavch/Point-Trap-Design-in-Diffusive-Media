module

public import TimeTraps.Analysis.SignedPeriodicPointPositiveGroundPhysical
public import TimeTraps.Analysis.SignedPeriodicPointVariationalNonnegative

@[expose] public section

/-! Every signed principal periodic weak eigenstate is determined
by one interior value. Absolute value and the independent variational
bound turn a zero of a principal state into the zero state. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.principal_hilbert_zero_of_interior_zero
    (P : SignedPeriodicPointProblem ι l r) (u : IntervalPeriodicSpace P.boundary)
    (he : ∀ v : IntervalPeriodicSpace P.boundary,
      P.form u v = P.principalValue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v))
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
      P.principalValue * ‖P.boundary.stateL (P.boundary.absState u)‖ ^ 2 := by
    rw [P.absState_form, P.boundary.absState_mass, he u, real_inner_self_eq_norm_sq]
  have hnonneg : ∀ y ∈ Icc l r,
      0 ≤ (P.boundary.absState u).val.representative P.boundary.interval_pos y := by
    intro y hy
    rw [P.boundary.absState_representative u hy]
    exact abs_nonneg _
  have hp := P.nonnegative_eigenstate_pos (P.boundary.absState u) P.principalValue ha hnonneg
    (P.minimizer_hilbert _ heq) x (Ioo_subset_Icc_self hx)
  rw [P.boundary.absState_representative u (Ioo_subset_Icc_self hx)] at hp
  change 0 < |u.val.representative P.boundary.interval_pos x| at hp
  rw [hz, abs_zero] at hp
  exact lt_irrefl 0 hp

theorem SignedPeriodicPointProblem.principal_hilbert_scalar
    (P : SignedPeriodicPointProblem ι l r) (u v : IntervalPeriodicSpace P.boundary)
    {x : ℝ} (hx : x ∈ Ioo l r) (hu₀ : u.val.representative P.boundary.interval_pos x ≠ 0)
    (hu : ∀ w : IntervalPeriodicSpace P.boundary,
      P.form u w = P.principalValue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL w))
    (hv : ∀ w : IntervalPeriodicSpace P.boundary,
      P.form v w = P.principalValue * inner ℝ (P.boundary.stateL v) (P.boundary.stateL w)) :
    v = (v.val.representative P.boundary.interval_pos x /
      u.val.representative P.boundary.interval_pos x) • u := by
  let c := v.val.representative P.boundary.interval_pos x / u.val.representative P.boundary.interval_pos x
  have he : ∀ w : IntervalPeriodicSpace P.boundary,
      P.form (v - c • u) w = P.principalValue *
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
  exact sub_eq_zero.mp (P.principal_hilbert_zero_of_interior_zero (v - c • u) he hx hz)

theorem SignedPeriodicPointProblem.principal_weak_scalar
    (P : SignedPeriodicPointProblem ι l r) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hv : IntervalEnergy v l r)
    (huz : u l = u r)
    (hvz : v l = v r)
    {x : ℝ} (hx : x ∈ Ioo l r) (hu₀ : u x ≠ 0)
    (heu : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      (w l = w r) →
      intervalPointForm P.diffusivity P.strength P.site l r u w =
        P.principalValue * ∫ y in l..r, u y * w y)
    (hev : ∀ w : ℝ → ℝ, IntervalEnergy w l r →
      (w l = w r) →
      intervalPointForm P.diffusivity P.strength P.site l r v w =
        P.principalValue * ∫ y in l..r, v y * w y) :
    EqOn v (fun y => (v x / u x) * u y) (Icc l r) := by
  have hUx := P.boundary.ofEnergy_representative hu huz.symm (Ioo_subset_Icc_self hx)
  have hVx := P.boundary.ofEnergy_representative hv hvz.symm (Ioo_subset_Icc_self hx)
  have hU₀ : (P.boundary.ofEnergy hu huz.symm).val.representative P.boundary.interval_pos x ≠ 0 := by
    rwa [hUx]
  have he := P.principal_hilbert_scalar (P.boundary.ofEnergy hu huz.symm) (P.boundary.ofEnergy hv hvz.symm)
    hx hU₀ (P.physical_eigen_hilbert hu huz P.principalValue heu) (P.physical_eigen_hilbert hv hvz P.principalValue hev)
  rw [hUx, hVx] at he
  intro y hy
  have he' := congrArg (fun w : IntervalPeriodicSpace P.boundary =>
    evalL P.boundary.interval_pos y hy w.val) he
  change evalL P.boundary.interval_pos y hy (P.boundary.ofEnergy hv hvz.symm).val =
    evalL P.boundary.interval_pos y hy ((v x / u x) • (P.boundary.ofEnergy hu huz.symm).val) at he'
  simp only [map_smul, smul_eq_mul] at he'
  change (P.boundary.ofEnergy hv hvz.symm).val.representative P.boundary.interval_pos y =
    (v x / u x) * (P.boundary.ofEnergy hu huz.symm).val.representative P.boundary.interval_pos y at he'
  rwa [P.boundary.ofEnergy_representative hu huz.symm hy,
    P.boundary.ofEnergy_representative hv hvz.symm hy] at he'

end TimeTraps.Analysis
