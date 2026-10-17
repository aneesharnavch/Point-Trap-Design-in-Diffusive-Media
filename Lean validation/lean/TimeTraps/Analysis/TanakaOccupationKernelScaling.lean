module

public import TimeTraps.Analysis.TanakaOccupationKernelConcentration
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-! Exact change of scale for the normalized occupation kernel. -/

namespace TimeTraps.Analysis

open MeasureTheory

theorem tanakaSmoothAbs_scale {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    tanakaSmoothAbs ε (ε * x) = ε * tanakaSmoothAbs 1 x := by
  unfold tanakaSmoothAbs
  rw [show (ε * x) ^ 2 + ε ^ 2 = ε ^ 2 * (x ^ 2 + 1 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]

theorem tanakaOccupationKernel_scale {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    tanakaOccupationKernel ε (ε * x) = ε⁻¹ * tanakaOccupationKernel 1 x := by
  unfold tanakaOccupationKernel
  rw [tanakaSmoothAbs_scale hε]
  have hs := (tanakaSmoothAbs_pos (by norm_num : (0 : ℝ) < 1) x).ne'
  field_simp

theorem tanakaOccupationKernel_average_scale {ε : ℝ} (hε : 0 < ε) (g : ℝ → ℝ) (x : ℝ) :
    (∫ y, tanakaOccupationKernel ε y * g (x - y)) =
      ∫ y, tanakaOccupationKernel 1 y * g (x - ε * y) := by
  have h := Measure.integral_comp_mul_left (fun y => tanakaOccupationKernel ε y * g (x - y)) ε
  have hf : (fun y => tanakaOccupationKernel ε (ε * y) * g (x - ε * y)) =
      fun y => ε⁻¹ * (tanakaOccupationKernel 1 y * g (x - ε * y)) := by
    funext y
    rw [tanakaOccupationKernel_scale hε]
    ring
  change (∫ y, tanakaOccupationKernel ε (ε * y) * g (x - ε * y)) = _ at h
  rw [hf, integral_const_mul] at h
  rw [abs_of_pos (inv_pos.mpr hε), smul_eq_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero hε.ne') h).symm

end TimeTraps.Analysis
