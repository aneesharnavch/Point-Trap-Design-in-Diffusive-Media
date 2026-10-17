module

public import TimeTraps.Analysis.IntervalEnergyAbsolute
public import TimeTraps.Analysis.IntervalEnergyLocal
public import TimeTraps.Analysis.FiniteKinkCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The absolute-value Green test is an actual full H¹ test. Splitting at
its kink and applying the absolute-continuity fundamental theorem gives
its exact derivative pairing, without any C² premise on the state. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem intervalEnergy_abs_sub (a l r : ℝ) (hlr : l ≤ r) :
    IntervalEnergy (fun x => |x - a|) l r := by
  have hi : IntervalEnergy (fun x => x - a) l r :=
    intervalEnergy_of_continuous_derivative (g := fun _ => 1) hlr
      (continuous_id.sub continuous_const).continuousOn continuousOn_const
      (fun x _ => (hasDerivAt_id x).sub_const a)
  exact hi.abs

theorem IntervalEnergy.abs_sub_pairing {u : ℝ → ℝ} {l r y : ℝ}
    (hu : IntervalEnergy u l r) (hy : y ∈ Icc l r) :
    (∫ x in l..r, deriv u x * deriv (fun z => |z - y|) x) =
      u r + u l - 2 * u y := by
  have hlr : l ≤ r := hy.1.trans hy.2
  have hsl : uIcc l y ⊆ uIcc l r := by
    rw [uIcc_of_le hy.1, uIcc_of_le hlr]
    exact Icc_subset_Icc le_rfl hy.2
  have hsr : uIcc y r ⊆ uIcc l r := by
    rw [uIcc_of_le hy.2, uIcc_of_le hlr]
    exact Icc_subset_Icc hy.1 le_rfl
  have hi : IntervalIntegrable (fun x => deriv u x * deriv (fun z => |z - y|) x) volume l r := by
    simpa only [one_mul] using
      hu.bilinear_integrable (intervalEnergy_abs_sub y l r hlr)
        (a := fun _ => 1) continuousOn_const
  have hleft : (∫ x in l..y, deriv u x * deriv (fun z => |z - y|) x) = -(u y - u l) := by
    calc
      _ = ∫ x in l..y, -deriv u x := by
        apply intervalIntegral.integral_congr_Ioo_of_le hy.1
        intro x hx
        dsimp only
        rw [(abs_sub_hasDerivAt_real_sign (ne_of_lt hx.2)).deriv,
          Real.sign_of_neg (sub_neg.mpr hx.2), mul_neg_one]
      _ = _ := by
        rw [intervalIntegral.integral_neg, (hu.mono hsl).absolutelyContinuous.integral_deriv_eq_sub]
  have hright : (∫ x in y..r, deriv u x * deriv (fun z => |z - y|) x) = u r - u y := by
    calc
      _ = ∫ x in y..r, deriv u x := by
        apply intervalIntegral.integral_congr_Ioo_of_le hy.2
        intro x hx
        dsimp only
        rw [(abs_sub_hasDerivAt_real_sign (ne_of_gt hx.1)).deriv,
          Real.sign_of_pos (sub_pos.mpr hx.1), mul_one]
      _ = _ := (hu.mono hsr).absolutelyContinuous.integral_deriv_eq_sub
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.mono_set hsl) (hi.mono_set hsr),
    hleft, hright]
  ring

theorem interval_integral_abs_sub {l r y : ℝ} (hy : y ∈ Icc l r) :
    (∫ x in l..r, |x - y|) = (y - l) ^ 2 / 2 + (r - y) ^ 2 / 2 := by
  have hc : Continuous (fun x : ℝ => |x - y|) := (continuous_id.sub continuous_const).abs
  have hleft : (∫ x in l..y, |x - y|) = (y - l) ^ 2 / 2 := by
    calc
      _ = ∫ x in l..y, y - x := by
        apply intervalIntegral.integral_congr_Ioo_of_le hy.1
        intro x hx
        dsimp only
        rw [abs_of_neg (sub_neg.mpr hx.2)]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun _ : ℝ => y) (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable l y)
          (continuous_id.intervalIntegrable l y), intervalIntegral.integral_const, integral_id]
        simp only [smul_eq_mul]
        ring
  have hright : (∫ x in y..r, |x - y|) = (r - y) ^ 2 / 2 := by
    calc
      _ = ∫ x in y..r, x - y := by
        apply intervalIntegral.integral_congr_Ioo_of_le hy.2
        intro x hx
        exact abs_of_pos (sub_pos.mpr hx.1)
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => y)
          (continuous_id.intervalIntegrable y r)
          (continuous_const.intervalIntegrable y r), integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable l y) (hc.intervalIntegrable y r), hleft, hright]

end TimeTraps.Analysis
