module

public import TimeTraps.Probability.BrownianOccupationL1Gaussian
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The Gaussian density peak has an integrable square-root singularity
at time zero. Its finite-time integral is computed exactly, including
the zero horizon. -/

namespace TimeTraps.Probability

open MeasureTheory

noncomputable def brownianOccupationL1Majorant (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * t ^ (-(1 / 2 : ℝ))

theorem brownianOccupationL1Majorant_eq_peak {t : ℝ} (ht : 0 ≤ t) :
    brownianOccupationL1Majorant t = (Real.sqrt (2 * Real.pi * t))⁻¹ := by
  rw [brownianOccupationL1Majorant, Real.rpow_neg ht, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), mul_inv_rev]
  exact mul_comm _ _

theorem brownianOccupationL1Majorant_intervalIntegrable (T : ℝ) :
    IntervalIntegrable brownianOccupationL1Majorant volume 0 T :=
  (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _

theorem brownianOccupationL1Majorant_integral (T : ℝ) :
    (∫ s in (0 : ℝ)..T, brownianOccupationL1Majorant s) =
      2 * Real.sqrt T / Real.sqrt (2 * Real.pi) := by
  unfold brownianOccupationL1Majorant
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero]
  rw [← Real.sqrt_eq_rpow]
  ring

end TimeTraps.Probability
