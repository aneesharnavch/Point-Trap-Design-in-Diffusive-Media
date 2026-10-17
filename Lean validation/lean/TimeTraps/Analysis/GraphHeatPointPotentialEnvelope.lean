module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The integrable one-dimensional short-time envelope and its exact
primitive. These elementary identities will dominate the actual graph
kernel at every closed spatial point. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

theorem inverseSqrt_eq_rpow_ae {T : ℝ} :
    (fun t : ℝ => 1 / Real.sqrt t) =ᵐ[volume.restrict (Ioc 0 T)]
      (fun t => t ^ (-(1 / 2) : ℝ)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow, one_div]

theorem inverseSqrt_intervalIntegrable {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt t) volume 0 T := by
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hr ⊢
  exact hr.congr inverseSqrt_eq_rpow_ae.symm

theorem inverseSqrt_integral {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, 1 / Real.sqrt t) = 2 * Real.sqrt T := by
  calc
    _ = ∫ t in (0 : ℝ)..T, t ^ (-(1 / 2) : ℝ) := by
      rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
      exact integral_congr_ae inverseSqrt_eq_rpow_ae
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
      norm_num
      rw [← Real.sqrt_eq_rpow]
      ring

theorem shortPointEnvelope_intervalIntegrable {T : ℝ} (hT : 0 ≤ T) (C : ℝ) :
    IntervalIntegrable (fun t : ℝ => C * (1 + 1 / Real.sqrt t)) volume 0 T :=
  (intervalIntegrable_const.add (inverseSqrt_intervalIntegrable hT)).const_mul C

theorem shortPointEnvelope_integral {T : ℝ} (hT : 0 ≤ T) (C : ℝ) :
    (∫ t in (0 : ℝ)..T, C * (1 + 1 / Real.sqrt t)) = C * (T + 2 * Real.sqrt T) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
    (inverseSqrt_intervalIntegrable hT), intervalIntegral.integral_const, inverseSqrt_integral hT]
  simp

end TimeTraps.Analysis
