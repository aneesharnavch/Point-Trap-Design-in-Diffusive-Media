module

public import TimeTraps.Analysis.ReversibleResistanceCoordinateInverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! Lebesgue transport through the actual resistance coordinate.
Its Jacobian is the original continuous conductance, and the time-change
speed therefore transports to the original physical speed density.
The tests and candidate occupation densities are arbitrary real functions. -/

namespace TimeTraps.Interval

open Set MeasureTheory

theorem IntervalMedium.resistanceInverse_integral (A : IntervalMedium) (g : ℝ → ℝ) :
    (∫ y in (0 : ℝ)..A.resistanceLength,
      g (A.resistanceInverse y) * A.conductance (A.resistanceInverse y)) =
      ∫ z in A.source.left..A.source.right, g z := by
  have hd : ∀ y ∈ Ioo (min (0 : ℝ) A.resistanceLength) (max 0 A.resistanceLength),
      HasDerivAt A.resistanceInverse (A.conductance (A.resistanceInverse y)) y := by
    simpa only [min_eq_left A.resistanceLength_pos.le, max_eq_right A.resistanceLength_pos.le]
      using fun y hy => A.resistanceInverse_hasDerivAt (y := y) hy
  have hi := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := g) A.resistanceInverse_continuous.continuousOn hd
      (fun y _ => (A.conductance_pos _ (A.resistanceInverse_mem y)).le)
  simpa only [Function.comp_apply, A.resistanceInverse_zero, A.resistanceInverse_length] using hi

theorem IntervalMedium.resistanceInverse_integrable_iff (A : IntervalMedium) (g : ℝ → ℝ) :
    IntervalIntegrable (fun y =>
      g (A.resistanceInverse y) * A.conductance (A.resistanceInverse y))
        volume 0 A.resistanceLength ↔
      IntervalIntegrable g volume A.source.left A.source.right := by
  have hd : ∀ y ∈ Ioo (min (0 : ℝ) A.resistanceLength) (max 0 A.resistanceLength),
      HasDerivAt A.resistanceInverse (A.conductance (A.resistanceInverse y)) y := by
    simpa only [min_eq_left A.resistanceLength_pos.le, max_eq_right A.resistanceLength_pos.le]
      using fun y hy => A.resistanceInverse_hasDerivAt (y := y) hy
  have hi := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (g := g) A.resistanceInverse_continuous.continuousOn hd
      (fun y _ => (A.conductance_pos _ (A.resistanceInverse_mem y)).le)
  simpa only [Function.comp_apply, A.resistanceInverse_zero, A.resistanceInverse_length] using hi

theorem IntervalMedium.resistance_density_transport (A : IntervalMedium)
    (g w : ℝ → ℝ) :
    (∫ z in A.source.left..A.source.right, g z * A.source.density z * w (A.resistance z)) =
      ∫ y in (0 : ℝ)..A.resistanceLength,
        g (A.resistanceInverse y) * A.resistanceSpeed y * w y := by
  rw [← A.resistanceInverse_integral (fun z => g z * A.source.density z * w (A.resistance z))]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Icc (0 : ℝ) A.resistanceLength := by
    simpa only [uIcc_of_le A.resistanceLength_pos.le] using hy
  change g (A.resistanceInverse y) * A.source.density (A.resistanceInverse y) *
      w (A.resistance (A.resistanceInverse y)) * A.conductance (A.resistanceInverse y) =
    g (A.resistanceInverse y) * A.resistanceSpeed y * w y
  rw [A.resistance_inverse hy']
  dsimp only [IntervalMedium.resistanceSpeed]
  ring

end TimeTraps.Interval
