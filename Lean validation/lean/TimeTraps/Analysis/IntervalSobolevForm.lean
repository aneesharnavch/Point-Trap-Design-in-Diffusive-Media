module

public import TimeTraps.Analysis.IntervalSobolevSpaceEvaluation
public import TimeTraps.Analysis.IntervalEnergyBoundedForm
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section

/-!
The source's unit-interval point-interaction form and constant source as
actual bounded linear maps on the independently constructed Hilbert H1
space. Their values agree with the original energy integrals and traces.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace
open scoped BigOperators

noncomputable section

abbrev UnitIntervalSobolev := IntervalSobolevSpace (0 : ℝ) 1

def unitSobolevGradientForm : UnitIntervalSobolev →L[ℝ] UnitIntervalSobolev →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (gradientL 0 1) (gradientL 0 1)

def unitSobolevForm {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1) :
    UnitIntervalSobolev →L[ℝ] UnitIntervalSobolev →L[ℝ] ℝ :=
  D • unitSobolevGradientForm +
    ∑ i, κ i • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (evalL zero_lt_one (z i) (hz i)) (evalL zero_lt_one (z i) (hz i))

def unitSobolevOne : IntervalSobolevL2 (0 : ℝ) 1 :=
  (memLp_const (1 : ℝ)).toLp (fun _ : ℝ => (1 : ℝ))

def unitSobolevSource : UnitIntervalSobolev →L[ℝ] ℝ :=
  (innerSL ℝ unitSobolevOne).comp (stateL 0 1)

theorem unitSobolev_gradient_pairing (u v : UnitIntervalSobolev) :
    inner ℝ u.gradient v.gradient = ∫ x in (0 : ℝ)..1,
      deriv (u.representative zero_lt_one) x * deriv (v.representative zero_lt_one) x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [(u.representative_spec zero_lt_one).2.2,
    (v.representative_spec zero_lt_one).2.2] with x hx hy
  simp only [Real.inner_apply, hx, hy]

theorem unitSobolevForm_apply {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1)
    (u v : UnitIntervalSobolev) :
    unitSobolevForm D κ z hz u v = unitPointForm D κ z
      (u.representative zero_lt_one) (v.representative zero_lt_one) := by
  simp only [unitSobolevForm, unitSobolevGradientForm, add_apply, smul_apply,
    sum_apply, ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply, ContinuousLinearMap.mul_apply', evalL_apply, smul_eq_mul]
  change D * inner ℝ u.gradient v.gradient +
    ∑ i, κ i * (u.representative zero_lt_one (z i) * v.representative zero_lt_one (z i)) = _
  rw [unitSobolev_gradient_pairing]
  simp only [unitPointForm, mul_assoc]

theorem unitSobolevSource_apply (u : UnitIntervalSobolev) :
    unitSobolevSource u = ∫ x in (0 : ℝ)..1, u.representative zero_lt_one x := by
  change inner ℝ unitSobolevOne u.state = _
  rw [L2.inner_def, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have h1 : unitSobolevOne =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] (fun _ => (1 : ℝ)) :=
    (memLp_const (1 : ℝ)).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [h1, (u.representative_spec zero_lt_one).2.1] with x hx hy
  simp only [Real.inner_apply, hx, hy, one_mul]

theorem unitSobolevForm_coercive {ι : Type*} [Fintype ι]
    {D : ℝ} (hD : 0 < D) (κ z : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1) (k : ι) (hκk : 0 < κ k) :
    IsCoercive (unitSobolevForm D κ z hz) := by
  refine ⟨min (D / 3) (κ k / 2), unitPointForm_coercivity_constant_pos hD hκk, ?_⟩
  intro u
  have h := (u.representative_spec zero_lt_one).1.unit_point_form_coercive hD.le hκ k (hz k)
  rw [← u.norm_sq_eq_h1SizeSq zero_lt_one, ← unitSobolevForm_apply D κ z hz u u] at h
  simpa only [pow_two, mul_assoc] using h

theorem unitSobolevSource_norm_le : ‖unitSobolevSource‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [Real.norm_eq_abs, unitSobolevSource_apply, one_mul, u.norm_eq_h1Size zero_lt_one]
  exact (u.representative_spec zero_lt_one).1.unit_source_bound

end

end TimeTraps.Analysis
