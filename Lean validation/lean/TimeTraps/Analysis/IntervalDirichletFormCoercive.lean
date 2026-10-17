module

public import TimeTraps.Analysis.IntervalDirichletForm

@[expose] public section

/-! A prescribed zero trace supplies coercivity without a positive contact.
The constant retains the actual interval length and controls the full H1
norm, not just the derivative seminorm. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

noncomputable instance intervalDirichletSpace_submoduleNormedSpace {l r : ℝ}
    (B : IntervalDirichletBoundary l r) :
    @NormedSpace ℝ (IntervalDirichletSpace B) Real.normedField
      (@Submodule.seminormedAddCommGroup ℝ (IntervalSobolevSpace l r) _
        (inferInstance : NormedAddCommGroup (IntervalSobolevSpace l r)).toSeminormedAddCommGroup
        _ B.subspace) := by
  letI : SeminormedAddCommGroup (IntervalSobolevSpace l r) :=
    (inferInstance : NormedAddCommGroup (IntervalSobolevSpace l r)).toSeminormedAddCommGroup
  exact Submodule.normedSpace B.subspace

theorem IntervalEnergy.h1_control_of_zero {u : ℝ → ℝ} {l r x : ℝ}
    (hu : IntervalEnergy u l r) (hx : x ∈ Icc l r) (hzero : u x = 0) :
    intervalH1SizeSq u l r ≤
      (2 * (r - l) ^ 2 + 1) * (∫ t in l..r, deriv u t ^ 2) := by
  simpa only [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] using hu.h1_control hx

theorem IntervalEnergy.interval_point_form_coercive_of_zero {ι : Type*} [Fintype ι]
    {D l r x : ℝ} {κ z : ι → ℝ} (hD : 0 ≤ D) (hκ : ∀ i, 0 ≤ κ i)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hx : x ∈ Icc l r) (hzero : u x = 0) :
    (D / (2 * (r - l) ^ 2 + 1)) * intervalH1SizeSq u l r ≤
      intervalPointForm D κ z l r u u := by
  have hA : 0 < 2 * (r - l) ^ 2 + 1 := by positivity
  calc
    _ ≤ (D / (2 * (r - l) ^ 2 + 1)) *
        ((2 * (r - l) ^ 2 + 1) * (∫ t in l..r, deriv u t ^ 2)) :=
      mul_le_mul_of_nonneg_left (hu.h1_control_of_zero hx hzero) (div_nonneg hD hA.le)
    _ = D * (∫ t in l..r, deriv u t ^ 2) := by
      rw [← mul_assoc, div_mul_cancel₀ D hA.ne']
    _ ≤ intervalPointForm D κ z l r u u := by
      rw [intervalPointForm_self]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hκ i) (sq_nonneg _))

theorem intervalDirichletPointForm_lower {ι : Type*} [Fintype ι] {l r D : ℝ}
    (B : IntervalDirichletBoundary l r) (hD : 0 ≤ D) (κ z : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hz : ∀ i, z i ∈ Icc l r) (u : IntervalDirichletSpace B) :
    (D / (2 * (r - l) ^ 2 + 1)) * ‖u‖ ^ 2 ≤ intervalDirichletPointForm B D κ z hz u u := by
  obtain ⟨x, hx⟩ := B.nonempty
  have hu := ((u : IntervalSobolevSpace l r).representative_spec B.interval_pos).1
  have h := hu.interval_point_form_coercive_of_zero (z := z)
    hD hκ (B.site_mem hx) (B.representative_zero u hx)
  rw [← (u : IntervalSobolevSpace l r).norm_sq_eq_h1SizeSq B.interval_pos,
    ← intervalDirichletPointForm_apply B D κ z hz u u] at h
  exact h

theorem intervalDirichletPointForm_coercive {ι : Type*} [Fintype ι] {l r D : ℝ}
    (B : IntervalDirichletBoundary l r) (hD : 0 < D) (κ z : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (hz : ∀ i, z i ∈ Icc l r) :
    @IsCoercive (IntervalDirichletSpace B) (Submodule.seminormedAddCommGroup B.subspace)
      (Submodule.normedSpace B.subspace) (intervalDirichletPointForm B D κ z hz) := by
  refine ⟨D / (2 * (r - l) ^ 2 + 1), div_pos hD (by positivity), ?_⟩
  intro u
  simpa only [pow_two, mul_assoc] using intervalDirichletPointForm_lower B hD.le κ z hκ hz u

end TimeTraps.Analysis
