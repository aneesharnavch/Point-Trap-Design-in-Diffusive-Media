module

public import TimeTraps.Analysis.IntervalEnergyCoercive
public import TimeTraps.Analysis.IntegralCauchySchwarz

@[expose] public section

/-!
Explicit boundedness of the source functional and point-interaction form
with respect to the actual H1 size. These are the quantitative estimates
needed to instantiate the abstract Hilbert-space existence theorem.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped BigOperators

theorem intervalH1Size_nonneg (u : ℝ → ℝ) (l r : ℝ) : 0 ≤ intervalH1Size u l r :=
  Real.sqrt_nonneg _

theorem interval_derivative_energy_le_h1 (u : ℝ → ℝ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, deriv u x ^ 2) ≤ intervalH1SizeSq u l r :=
  le_add_of_nonneg_left (intervalIntegral.integral_nonneg_of_forall hlr
    (fun x => sq_nonneg (u x)))

theorem IntervalEnergy.unit_source_bound {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1) :
    |∫ x in (0 : ℝ)..1, u x| ≤ intervalH1Size u 0 1 := by
  have h := interval_integral_sq_le_length_mul zero_le_one
    hu.continuousOn.intervalIntegrable hu.state_square_integrable
  have hE : 0 ≤ ∫ x in (0 : ℝ)..1, deriv u x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => sq_nonneg (deriv u x))
  apply (sq_le_sq₀ (abs_nonneg _) (intervalH1Size_nonneg u 0 1)).mp
  rw [sq_abs, intervalH1Size_sq u zero_le_one]
  unfold intervalH1SizeSq
  simp only [sub_zero, one_mul] at h
  linarith

theorem IntervalEnergy.unit_derivative_pair_bound {u v : ℝ → ℝ}
    (hu : IntervalEnergy u 0 1) (hv : IntervalEnergy v 0 1) :
    |∫ x in (0 : ℝ)..1, deriv u x * deriv v x| ≤
      intervalH1Size u 0 1 * intervalH1Size v 0 1 := by
  have h := interval_integral_mul_sq_le zero_le_one hu.derivative_memLp hv.derivative_memLp
  have hEv : 0 ≤ ∫ x in (0 : ℝ)..1, deriv v x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => sq_nonneg (deriv v x))
  have hm := mul_le_mul (interval_derivative_energy_le_h1 u zero_le_one)
    (interval_derivative_energy_le_h1 v zero_le_one) hEv
    (intervalH1SizeSq_nonneg u zero_le_one)
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (intervalH1Size_nonneg u 0 1)
    (intervalH1Size_nonneg v 0 1))).mp
  rw [sq_abs, mul_pow, intervalH1Size_sq u zero_le_one, intervalH1Size_sq v zero_le_one]
  exact h.trans hm

theorem IntervalEnergy.unit_point_pair_bound {u v : ℝ → ℝ} {x : ℝ}
    (hu : IntervalEnergy u 0 1) (hv : IntervalEnergy v 0 1) (hx : x ∈ Icc 0 1) :
    |u x * v x| ≤ 2 * (intervalH1Size u 0 1 * intervalH1Size v 0 1) := by
  have h := mul_le_mul (hu.unit_trace_abs_le hx) (hv.unit_trace_abs_le hx)
    (abs_nonneg (v x)) (mul_nonneg (Real.sqrt_nonneg _) (intervalH1Size_nonneg u 0 1))
  rw [abs_mul]
  calc
    |u x| * |v x| ≤ (Real.sqrt 2 * intervalH1Size u 0 1) *
        (Real.sqrt 2 * intervalH1Size v 0 1) := h
    _ = Real.sqrt 2 ^ 2 * (intervalH1Size u 0 1 * intervalH1Size v 0 1) := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The manuscript's bilinear form is bounded on the full signed energy class. -/
theorem IntervalEnergy.unit_point_form_bound {ι : Type*} [Fintype ι]
    {D : ℝ} {κ z : ι → ℝ} (hD : 0 ≤ D) (hκ : ∀ i, 0 ≤ κ i)
    (hz : ∀ i, z i ∈ Icc 0 1) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u 0 1) (hv : IntervalEnergy v 0 1) :
    |unitPointForm D κ z u v| ≤
      (D + 2 * ∑ i, κ i) * (intervalH1Size u 0 1 * intervalH1Size v 0 1) := by
  classical
  let H := intervalH1Size u 0 1 * intervalH1Size v 0 1
  have hd : |D * (∫ x in (0 : ℝ)..1, deriv u x * deriv v x)| ≤ D * H := by
    rw [abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left (hu.unit_derivative_pair_bound hv) hD
  have hp : |∑ i, κ i * u (z i) * v (z i)| ≤ (2 * ∑ i, κ i) * H := by
    calc
      |∑ i, κ i * u (z i) * v (z i)| ≤ ∑ i, |κ i * u (z i) * v (z i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, κ i * (2 * H) := by
        apply Finset.sum_le_sum
        intro i _
        rw [mul_assoc, abs_mul, abs_of_nonneg (hκ i)]
        exact mul_le_mul_of_nonneg_left (hu.unit_point_pair_bound hv (hz i)) (hκ i)
      _ = _ := by rw [← Finset.sum_mul]; ring
  unfold unitPointForm
  calc
    _ ≤ |D * (∫ x in (0 : ℝ)..1, deriv u x * deriv v x)| +
        |∑ i, κ i * u (z i) * v (z i)| := abs_add_le _ _
    _ ≤ D * H + (2 * ∑ i, κ i) * H := add_le_add hd hp
    _ = _ := by ring

end TimeTraps.Analysis
