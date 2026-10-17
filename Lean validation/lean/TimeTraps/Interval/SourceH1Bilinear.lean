module

public import TimeTraps.Interval.SourceH1Coordinate
public import TimeTraps.Interval.SourceMeanPullbackGeometry

@[expose] public section

/-! Exact transport of the full H1 bilinear form. The physical form is the
source mass times the effective unit-coordinate form, with no regularity
assumed beyond energy-space membership for either function. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis

theorem source_h1_bilinear (A : IntervalMedium) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u A.source.left A.source.right)
    (hv : IntervalEnergy v A.source.left A.source.right) :
    (∫ x in A.source.left..A.source.right, A.conductance x * deriv u x * deriv v x) =
      A.source.mass * ∫ z in (0 : ℝ)..1, sourceMeanConductance A z *
        deriv (A.source.transformed u) z * deriv (A.source.transformed v) z := by
  have hd : ∀ z ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt A.source.inverse (A.source.mass / A.source.density (A.source.inverse z)) z := by
    simp only [min_eq_left zero_le_one, max_eq_right zero_le_one]
    exact fun _ hz => A.source.inverse_derivative hz
  have hp : ∀ z ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      0 ≤ A.source.mass / A.source.density (A.source.inverse z) :=
    fun z _ => (div_pos A.source.mass_pos (A.source.positive _ (A.source.inverse_mem z))).le
  have hi := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := A.source.inverse) (f' := fun z => A.source.mass / A.source.density (A.source.inverse z))
    (g := fun x => A.conductance x * deriv u x * deriv v x)
    A.source.inverse_continuous.continuousOn hd hp
  simp only [Function.comp_apply, A.source.inverse_zero, A.source.inverse_one] at hi
  rw [← hi, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(source_h1_inverse A.source hu).2, (source_h1_inverse A.source hv).2,
    volume.ae_ne (1 : ℝ)] with z hzu hzv hzne hz
  have hzi : z ∈ Ioo (0 : ℝ) 1 := by
    have hz' : z ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hz
    exact ⟨hz'.1, lt_of_le_of_ne hz'.2 hzne⟩
  rw [hzu hzi, hzv hzi]
  change (A.conductance (A.source.inverse z) * deriv u (A.source.inverse z) * deriv v (A.source.inverse z)) *
      (A.source.mass / A.source.density (A.source.inverse z)) =
    A.source.mass * ((1 / (A.source.mass ^ 2 /
      (A.conductance (A.source.inverse z) * A.source.density (A.source.inverse z)))) *
      (deriv u (A.source.inverse z) * (A.source.mass / A.source.density (A.source.inverse z))) *
      (deriv v (A.source.inverse z) * (A.source.mass / A.source.density (A.source.inverse z))))
  field_simp [ne_of_gt A.source.mass_pos, ne_of_gt (A.source.positive _ (A.source.inverse_mem z)),
    ne_of_gt (A.conductance_pos _ (A.source.inverse_mem z))]

end TimeTraps.Interval
