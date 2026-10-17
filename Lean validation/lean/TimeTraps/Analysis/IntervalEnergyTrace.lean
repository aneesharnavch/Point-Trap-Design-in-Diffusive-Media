module

public import TimeTraps.Analysis.IntervalEnergyEstimates

@[expose] public section

/-!
Point Poincaré and trace inequalities, with the constants used in the
foundational chapter. The squared H1 size is defined by the two actual
Lebesgue integrals; no norm or trace-continuity assumption is built in.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

noncomputable def intervalH1SizeSq (u : ℝ → ℝ) (l r : ℝ) : ℝ :=
  (∫ x in l..r, u x ^ 2) + (∫ x in l..r, deriv u x ^ 2)

noncomputable def intervalH1Size (u : ℝ → ℝ) (l r : ℝ) : ℝ :=
  Real.sqrt (intervalH1SizeSq u l r)

theorem intervalH1SizeSq_nonneg (u : ℝ → ℝ) {l r : ℝ} (hlr : l ≤ r) :
    0 ≤ intervalH1SizeSq u l r :=
  add_nonneg (intervalIntegral.integral_nonneg_of_forall hlr (fun x => sq_nonneg (u x)))
    (intervalIntegral.integral_nonneg_of_forall hlr (fun x => sq_nonneg (deriv u x)))

theorem intervalH1Size_sq (u : ℝ → ℝ) {l r : ℝ} (hlr : l ≤ r) :
    intervalH1Size u l r ^ 2 = intervalH1SizeSq u l r :=
  Real.sq_sqrt (intervalH1SizeSq_nonneg u hlr)

theorem IntervalEnergy.point_sq_le {u : ℝ → ℝ} {l r x z : ℝ}
    (hu : IntervalEnergy u l r) (hx : x ∈ Icc l r) (hz : z ∈ Icc l r) :
    u x ^ 2 ≤ 2 * u z ^ 2 + 2 * (r - l) * (∫ t in l..r, deriv u t ^ 2) := by
  have hE : 0 ≤ ∫ t in l..r, deriv u t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (hx.1.trans hx.2) (fun t => sq_nonneg _)
  have hdist : |x - z| ≤ r - l := abs_le.mpr ⟨by linarith [hx.1, hz.2],
    by linarith [hx.2, hz.1]⟩
  have hd := (hu.sub_sq_le hx hz).trans (mul_le_mul_of_nonneg_right hdist hE)
  nlinarith [sq_nonneg (u x - 2 * u z)]

/-- Point Poincaré on an arbitrary compact interval. -/
theorem IntervalEnergy.point_poincare {u : ℝ → ℝ} {l r z : ℝ}
    (hu : IntervalEnergy u l r) (hz : z ∈ Icc l r) :
    (∫ x in l..r, u x ^ 2) ≤
      2 * (r - l) * u z ^ 2 + 2 * (r - l) ^ 2 * (∫ t in l..r, deriv u t ^ 2) := by
  have h := intervalIntegral.integral_mono_on (hz.1.trans hz.2)
    hu.state_square_integrable intervalIntegrable_const
    (fun x hx => hu.point_sq_le hx hz)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  convert h using 1
  ring

/-- The full H1 square is controlled by a point value and derivative energy. -/
theorem IntervalEnergy.h1_control {u : ℝ → ℝ} {l r z : ℝ}
    (hu : IntervalEnergy u l r) (hz : z ∈ Icc l r) :
    intervalH1SizeSq u l r ≤ 2 * (r - l) * u z ^ 2 +
      (2 * (r - l) ^ 2 + 1) * (∫ t in l..r, deriv u t ^ 2) := by
  have h := hu.point_poincare hz
  unfold intervalH1SizeSq
  linarith

/-- Point evaluation is controlled by both L2 terms, with an explicit interval
length constant. This includes evaluations at the reflecting endpoints. -/
theorem IntervalEnergy.trace_sq_le {u : ℝ → ℝ} {l r x : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hx : x ∈ Icc l r) :
    u x ^ 2 ≤ (2 / (r - l)) * (∫ t in l..r, u t ^ 2) +
      2 * (r - l) * (∫ t in l..r, deriv u t ^ 2) := by
  have h := intervalIntegral.integral_mono_on hlr.le intervalIntegrable_const
    ((hu.state_square_integrable.const_mul 2).add intervalIntegrable_const)
    (fun z hz => hu.point_sq_le hx hz)
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hu.state_square_integrable.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  calc
    u x ^ 2 ≤ (2 * (∫ t in l..r, u t ^ 2) +
        (r - l) * (2 * (r - l) * (∫ t in l..r, deriv u t ^ 2))) / (r - l) :=
      (le_div_iff₀ (sub_pos.mpr hlr)).mpr (by nlinarith)
    _ = _ := by
      field_simp

/-- Exact unit-interval point Poincaré constant from the manuscript. -/
theorem IntervalEnergy.unit_point_poincare {u : ℝ → ℝ} {z : ℝ}
    (hu : IntervalEnergy u 0 1) (hz : z ∈ Icc 0 1) :
    (∫ x in (0 : ℝ)..1, u x ^ 2) ≤
      2 * u z ^ 2 + 2 * (∫ x in (0 : ℝ)..1, deriv u x ^ 2) := by
  simpa only [sub_zero, one_pow, mul_one] using hu.point_poincare hz

theorem IntervalEnergy.unit_h1_control {u : ℝ → ℝ} {z : ℝ}
    (hu : IntervalEnergy u 0 1) (hz : z ∈ Icc 0 1) :
    intervalH1SizeSq u 0 1 ≤ 2 * u z ^ 2 + 3 * (∫ x in (0 : ℝ)..1, deriv u x ^ 2) := by
  have h := hu.h1_control hz
  norm_num at h
  exact h

theorem IntervalEnergy.unit_trace_sq_le {u : ℝ → ℝ} {x : ℝ}
    (hu : IntervalEnergy u 0 1) (hx : x ∈ Icc 0 1) :
    u x ^ 2 ≤ 2 * intervalH1SizeSq u 0 1 := by
  have h := hu.trace_sq_le zero_lt_one hx
  simp only [sub_zero, div_one, mul_one] at h
  unfold intervalH1SizeSq
  linarith

theorem IntervalEnergy.unit_trace_abs_le {u : ℝ → ℝ} {x : ℝ}
    (hu : IntervalEnergy u 0 1) (hx : x ∈ Icc 0 1) :
    |u x| ≤ Real.sqrt 2 * intervalH1Size u 0 1 := by
  have h := hu.unit_trace_sq_le hx
  have hs := intervalH1Size_sq u (zero_le_one : (0 : ℝ) ≤ 1)
  have hr : (Real.sqrt 2 * intervalH1Size u 0 1) ^ 2 =
      2 * intervalH1SizeSq u 0 1 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hs]
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  change |u x| ^ 2 ≤ (Real.sqrt 2 * intervalH1Size u 0 1) ^ 2
  simpa only [sq_abs, hr] using h

end TimeTraps.Analysis
