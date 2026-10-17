module

public import TimeTraps.Analysis.IntervalEnergyTrace

@[expose] public section

/-!
The exact coercivity constant in the unit-interval foundational argument.
The point-interaction form below is its actual integral and finite sum.
Only one strictly positive interaction is needed; all others may be zero.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped BigOperators

noncomputable def unitPointForm {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (u v : ℝ → ℝ) : ℝ :=
  D * (∫ x in (0 : ℝ)..1, deriv u x * deriv v x) + ∑ i, κ i * u (z i) * v (z i)

theorem unitPointForm_self {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (u : ℝ → ℝ) :
    unitPointForm D κ z u u =
      D * (∫ x in (0 : ℝ)..1, deriv u x ^ 2) + ∑ i, κ i * u (z i) ^ 2 := by
  simp only [unitPointForm, pow_two, mul_assoc]

theorem unitPointForm_lower_single {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (u : ℝ → ℝ) (k : ι) :
    D * (∫ x in (0 : ℝ)..1, deriv u x ^ 2) + κ k * u (z k) ^ 2 ≤
      unitPointForm D κ z u u := by
  classical
  rw [unitPointForm_self]
  exact add_le_add le_rfl
    (Finset.single_le_sum (fun i _ => mul_nonneg (hκ i) (sq_nonneg (u (z i)))) (Finset.mem_univ k))

theorem unitPointForm_coercivity_constant_pos {D κ : ℝ} (hD : 0 < D) (hκ : 0 < κ) :
    0 < min (D / 3) (κ / 2) :=
  lt_min (div_pos hD (by norm_num)) (div_pos hκ (by norm_num))

/-- Exact constant min(D/3,κₖ/2), with the manuscript's H1 square. -/
theorem IntervalEnergy.unit_point_form_coercive {ι : Type*} [Fintype ι]
    {D : ℝ} {κ z : ι → ℝ} (hD : 0 ≤ D) (hκ : ∀ i, 0 ≤ κ i)
    {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1) (k : ι) (hz : z k ∈ Icc 0 1) :
    min (D / 3) (κ k / 2) * intervalH1SizeSq u 0 1 ≤ unitPointForm D κ z u u := by
  let c := min (D / 3) (κ k / 2)
  have hc : 0 ≤ c := le_min (div_nonneg hD (by norm_num))
    (div_nonneg (hκ k) (by norm_num))
  have hcD : 3 * c ≤ D := by
    have h := min_le_left (D / 3) (κ k / 2)
    dsimp only [c]
    linarith
  have hck : 2 * c ≤ κ k := by
    have h := min_le_right (D / 3) (κ k / 2)
    dsimp only [c]
    linarith
  have hE : 0 ≤ ∫ x in (0 : ℝ)..1, deriv u x ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall zero_le_one (fun x => sq_nonneg (deriv u x))
  have hcontrol := mul_le_mul_of_nonneg_left (hu.unit_h1_control hz) hc
  have hderiv := mul_le_mul_of_nonneg_right hcD hE
  have hpoint := mul_le_mul_of_nonneg_right hck (sq_nonneg (u (z k)))
  have hlower := unitPointForm_lower_single D κ z hκ u k
  change c * intervalH1SizeSq u 0 1 ≤ _
  nlinarith

/-- A nonzero value anywhere forces strictly positive form energy. -/
theorem IntervalEnergy.unit_point_form_pos {ι : Type*} [Fintype ι]
    {D : ℝ} {κ z : ι → ℝ} (hD : 0 < D) (hκ : ∀ i, 0 ≤ κ i)
    {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1) (k : ι)
    (hκk : 0 < κ k) (hz : z k ∈ Icc 0 1)
    {x : ℝ} (hx : x ∈ Icc 0 1) (hux : u x ≠ 0) :
    0 < unitPointForm D κ z u u := by
  have htrace := hu.unit_trace_sq_le hx
  have hsize : 0 < intervalH1SizeSq u 0 1 := by
    have hs : 0 < u x ^ 2 := sq_pos_of_ne_zero hux
    linarith
  exact (mul_pos (unitPointForm_coercivity_constant_pos hD hκk) hsize).trans_le
    (hu.unit_point_form_coercive hD.le hκ k hz)

/-- Evaluation differences obey the same explicit H1 bound. -/
theorem IntervalEnergy.unit_trace_difference {u v : ℝ → ℝ} {x : ℝ}
    (hu : IntervalEnergy u 0 1) (hv : IntervalEnergy v 0 1) (hx : x ∈ Icc 0 1) :
    |u x - v x| ≤ Real.sqrt 2 * intervalH1Size (fun y => u y - v y) 0 1 :=
  (hu.sub hv).unit_trace_abs_le hx

end TimeTraps.Analysis
