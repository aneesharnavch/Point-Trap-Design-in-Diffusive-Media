module

public import TimeTraps.Analysis.SourceCoordinate
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-!
Exact transport of derivatives and integrals to source coordinates. The
transformed weight retains the physical conductance and source profile.
Change of variables uses interior derivatives and closed-interval continuity,
so no differentiability of either medium coefficient is required.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

noncomputable def SourceInterval.transformed (P : SourceInterval) (u : ℝ → ℝ) : ℝ → ℝ :=
  u ∘ P.inverse

noncomputable def SourceInterval.weight (P : SourceInterval) (a : ℝ → ℝ) (z : ℝ) : ℝ :=
  P.mass ^ 2 / (a (P.inverse z) * P.density (P.inverse z))

theorem SourceInterval.transformed_continuous (P : SourceInterval) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc P.left P.right)) : Continuous (P.transformed u) :=
  hu.comp_continuous P.inverse_continuous P.inverse_mem

theorem SourceInterval.transformed_coordinate (P : SourceInterval) (u : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Icc P.left P.right) : P.transformed u (P.coordinate x) = u x := by
  simp only [SourceInterval.transformed, Function.comp_apply, P.inverse_coordinate hx]

theorem SourceInterval.transformed_derivative (P : SourceInterval) {u : ℝ → ℝ} {z d : ℝ}
    (hz : z ∈ Ioo 0 1) (hu : HasDerivAt u d (P.inverse z)) :
    HasDerivAt (P.transformed u) (d * (P.mass / P.density (P.inverse z))) z :=
  hu.comp z (P.inverse_derivative hz)

theorem SourceInterval.weight_pos (P : SourceInterval) {a : ℝ → ℝ}
    (ha : ∀ x ∈ Icc P.left P.right, 0 < a x) (z : ℝ) : 0 < P.weight a z :=
  div_pos (sq_pos_of_pos P.mass_pos)
    (mul_pos (ha _ (P.inverse_mem z)) (P.positive _ (P.inverse_mem z)))

theorem SourceInterval.weight_continuous (P : SourceInterval) {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc P.left P.right))
    (hapos : ∀ x ∈ Icc P.left P.right, 0 < a x) : Continuous (P.weight a) :=
  continuous_const.div ((P.transformed_continuous ha).mul (P.transformed_continuous P.continuous))
    (fun z => ne_of_gt (mul_pos (hapos _ (P.inverse_mem z)) (P.positive _ (P.inverse_mem z))))

theorem SourceInterval.coordinate_substitution (P : SourceInterval) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) :
    (∫ x in P.left..P.right, g (P.coordinate x) * (P.density x / P.mass)) = ∫ z in 0..1, g z := by
  have hi := intervalIntegral.integral_comp_mul_deriv''
    (a := P.left) (b := P.right) (f := P.coordinate) (f' := fun x => P.density x / P.mass) (g := g)
    (by simpa only [uIcc_of_le P.increasing.le] using P.coordinate_continuous)
    (by
      intro x hx
      apply (P.coordinate_derivative ?_).hasDerivWithinAt
      simpa only [min_eq_left P.increasing.le, max_eq_right P.increasing.le] using hx)
    (by simpa only [uIcc_of_le P.increasing.le] using P.continuous.div_const P.mass)
    (by simpa only [uIcc_of_le P.increasing.le, P.coordinate_image] using hg)
  simpa only [Function.comp_apply, P.coordinate_left, P.coordinate_right] using hi

theorem SourceInterval.inverse_substitution (P : SourceInterval) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc P.left P.right)) :
    (∫ z in 0..1, g (P.inverse z) * (P.mass / P.density (P.inverse z))) =
      ∫ x in P.left..P.right, g x := by
  have hj : Continuous (fun z => P.mass / P.density (P.inverse z)) :=
    continuous_const.div (P.transformed_continuous P.continuous)
      (fun z => ne_of_gt (P.positive _ (P.inverse_mem z)))
  have hi := intervalIntegral.integral_comp_mul_deriv''
    (a := 0) (b := 1) (f := P.inverse) (f' := fun z => P.mass / P.density (P.inverse z)) (g := g)
    P.inverse_continuous.continuousOn
    (by
      intro z hz
      apply (P.inverse_derivative ?_).hasDerivWithinAt
      simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hz)
    hj.continuousOn
    (by simpa only [uIcc_of_le zero_le_one, P.inverse_image] using hg)
  simpa only [Function.comp_apply, P.inverse_zero, P.inverse_one] using hi

/-- The source measure becomes constant mass times ordinary unit-interval
measure. This is an identity of exact integrals, not sampled values. -/
theorem SourceInterval.source_integral (P : SourceInterval) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc P.left P.right)) :
    (∫ x in P.left..P.right, P.density x * g x) =
      P.mass * ∫ z in 0..1, P.transformed g z := by
  calc
    _ = ∫ z in 0..1, (P.density (P.inverse z) * g (P.inverse z)) *
        (P.mass / P.density (P.inverse z)) := (P.inverse_substitution (P.continuous.mul hg)).symm
    _ = ∫ z in 0..1, P.mass * P.transformed g z := by
      apply intervalIntegral.integral_congr
      intro z _
      unfold SourceInterval.transformed
      simp only [Function.comp_apply]
      field_simp [ne_of_gt (P.positive _ (P.inverse_mem z))]
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- The profile retains the total resistance: the integral of Ω is mass
times the physical resistance integral. -/
theorem SourceInterval.weight_integral (P : SourceInterval) {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc P.left P.right))
    (hapos : ∀ x ∈ Icc P.left P.right, 0 < a x) :
    (∫ z in 0..1, P.weight a z) = P.mass * resistancePrimitive a P.left P.right := by
  have hi := P.inverse_substitution (g := fun x => 1 / a x)
    (continuousOn_const.div ha (fun x hx => ne_of_gt (hapos x hx)))
  calc
    _ = ∫ z in 0..1, P.mass * ((1 / a (P.inverse z)) *
        (P.mass / P.density (P.inverse z))) := by
      apply intervalIntegral.integral_congr
      intro z _
      unfold SourceInterval.weight
      ring
    _ = P.mass * ∫ z in 0..1, (1 / a (P.inverse z)) *
        (P.mass / P.density (P.inverse z)) := intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [hi]; rfl

end TimeTraps.Analysis
