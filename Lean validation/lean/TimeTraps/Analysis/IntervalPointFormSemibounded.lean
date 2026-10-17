module

public import TimeTraps.Analysis.IntervalEnergyTraceInterpolation
public import TimeTraps.Analysis.IntervalPointForm

@[expose] public section

/-! Explicit semiboundedness and a coercive mass shift for the actual finite
point form with arbitrary real strengths. No positive contact is required;
the finite family may be empty. All estimates concern full signed H1 states. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def intervalPointStrengthSize (κ : ι → ℝ) : ℝ := ∑ i, |κ i|

noncomputable def intervalPointNegativeBound (D : ℝ) (κ : ι → ℝ) (l r : ℝ) : ℝ :=
  intervalPointStrengthSize κ *
    (2 / (r - l) + 8 * (intervalPointStrengthSize κ + 1) / D)

theorem intervalPointStrengthSize_nonneg (κ : ι → ℝ) : 0 ≤ intervalPointStrengthSize κ :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (κ i))

theorem intervalPointNegativeBound_nonneg {D l r : ℝ} (hD : 0 < D) (hlr : l < r)
    (κ : ι → ℝ) : 0 ≤ intervalPointNegativeBound D κ l r := by
  unfold intervalPointNegativeBound
  have hA := intervalPointStrengthSize_nonneg κ
  positivity

theorem IntervalEnergy.point_form_lower_interpolation {u : ℝ → ℝ} {l r ε : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hε : 0 < ε)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) :
    (D - 2 * ε * intervalPointStrengthSize κ) * (∫ t in l..r, deriv u t ^ 2) -
      intervalPointStrengthSize κ * (2 / (r - l) + 2 / ε) * (∫ t in l..r, u t ^ 2) ≤
        intervalPointForm D κ z l r u u := by
  let S := (2 / (r - l) + 2 / ε) * (∫ t in l..r, u t ^ 2) +
    2 * ε * (∫ t in l..r, deriv u t ^ 2)
  have hs : -(intervalPointStrengthSize κ * S) ≤ ∑ i, κ i * u (z i) ^ 2 := by
    calc
      _ = ∑ i, -(|κ i| * S) := by
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
        rfl
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have ht : u (z i) ^ 2 ≤ S := hu.trace_sq_interpolation hlr (hz i) hε
        have hmul := mul_le_mul_of_nonneg_left ht (abs_nonneg (κ i))
        have hk := mul_le_mul_of_nonneg_right (neg_abs_le (κ i)) (sq_nonneg (u (z i)))
        nlinarith
  rw [intervalPointForm_self]
  dsimp only [S] at hs
  nlinarith

/-- The negative contacts consume at most half the derivative energy after
the stated explicit mass bound is subtracted. -/
theorem IntervalEnergy.point_form_derivative_lower {u : ℝ → ℝ} {l r D : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hD : 0 < D)
    (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) :
    (D / 2) * (∫ t in l..r, deriv u t ^ 2) -
      intervalPointNegativeBound D κ l r * (∫ t in l..r, u t ^ 2) ≤
        intervalPointForm D κ z l r u u := by
  let A := intervalPointStrengthSize κ
  let ε := D / (4 * (A + 1))
  have hA : 0 ≤ A := intervalPointStrengthSize_nonneg κ
  have hA1 : 0 < A + 1 := by linarith
  have hε : 0 < ε := div_pos hD (mul_pos (by norm_num) hA1)
  have he : 2 * ε * (A + 1) = D / 2 := by
    dsimp only [ε]
    field_simp
    norm_num
  have heA : 2 * ε * A ≤ D / 2 := by nlinarith
  have hr : 2 / ε = 8 * (A + 1) / D := by
    dsimp only [ε]
    field_simp
    norm_num
  have h := hu.point_form_lower_interpolation hlr hε D κ z hz
  change (D - 2 * ε * A) * (∫ t in l..r, deriv u t ^ 2) -
    A * (2 / (r - l) + 2 / ε) * (∫ t in l..r, u t ^ 2) ≤ _ at h
  rw [hr] at h
  have hE : 0 ≤ ∫ t in l..r, deriv u t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg (deriv u t))
  have hd := mul_le_mul_of_nonneg_right heA hE
  change D / 2 * (∫ t in l..r, deriv u t ^ 2) -
    (A * (2 / (r - l) + 8 * (A + 1) / D)) * (∫ t in l..r, u t ^ 2) ≤ _
  nlinarith

theorem IntervalEnergy.point_form_semibounded {u : ℝ → ℝ} {l r D : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hD : 0 < D)
    (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) :
    -(intervalPointNegativeBound D κ l r * (∫ t in l..r, u t ^ 2)) ≤
      intervalPointForm D κ z l r u u := by
  have h := hu.point_form_derivative_lower hlr hD κ z hz
  have hE : 0 ≤ ∫ t in l..r, deriv u t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg (deriv u t))
  have hp := mul_nonneg (div_nonneg hD.le (by norm_num : (0 : ℝ) ≤ 2)) hE
  linarith

/-- Adding the explicit mass coefficient C+1 gives a positive coercivity
constant on the original H1 norm, independently of the contact signs. -/
theorem IntervalEnergy.point_form_shift_coercive {u : ℝ → ℝ} {l r D : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hD : 0 < D)
    (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) :
    min (D / 2) 1 * intervalH1SizeSq u l r ≤
      intervalPointForm D κ z l r u u +
        (intervalPointNegativeBound D κ l r + 1) * (∫ t in l..r, u t ^ 2) := by
  have h := hu.point_form_derivative_lower hlr hD κ z hz
  have hM : 0 ≤ ∫ t in l..r, u t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg (u t))
  have hE : 0 ≤ ∫ t in l..r, deriv u t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg (deriv u t))
  have hm := mul_le_mul_of_nonneg_right (min_le_right (D / 2) 1) hM
  have hd := mul_le_mul_of_nonneg_right (min_le_left (D / 2) 1) hE
  unfold intervalH1SizeSq
  nlinarith

end TimeTraps.Analysis
