module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandData
public import TimeTraps.Probability.ReversibleResistancePhysicalBandErrorAverage

@[expose] public section

/-! A deterministic weighted-average estimate with the exact speed-mass
denominator. The denominator is not replaced by Euclidean band width. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem speedMass_average_error_bound {μ : Measure ℝ} {f w e : ℝ → ℝ} (c : ℝ)
    (hf : Integrable f μ) (hw : Integrable w μ) (he : Integrable e μ)
    (hwpos : 0 < ∫ z, w z ∂μ) (hb : ∀ᵐ z ∂μ, |f z - w z * c| ≤ e z / 2) :
    |(∫ z, f z ∂μ) / (∫ z, w z ∂μ) - c| ≤
      (∫ z, e z ∂μ) / (2 * ∫ z, w z ∂μ) := by
  have hdiv : Integrable (fun z => e z / 2) μ := by
    simpa only [div_eq_mul_inv] using he.mul_const (2 : ℝ)⁻¹
  have hi : |∫ z, (f z - w z * c) ∂μ| ≤ (∫ z, e z ∂μ) / 2 := by
    rw [← integral_div]
    simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le (f := fun z => f z - w z * c) hdiv hb
  have heq : (∫ z, f z ∂μ) / (∫ z, w z ∂μ) - c =
      (1 / (∫ z, w z ∂μ)) * ∫ z, (f z - w z * c) ∂μ := by
    rw [integral_sub hf (hw.mul_const c), integral_mul_const]
    field_simp
  rw [heq, abs_mul, abs_of_pos (one_div_pos.mpr hwpos)]
  calc
    _ ≤ (1 / (∫ z, w z ∂μ)) * ((∫ z, e z ∂μ) / 2) :=
      mul_le_mul_of_nonneg_left hi (one_div_pos.mpr hwpos).le
    _ = _ := by ring

theorem resistancePhysicalBand_average_error_ratio (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) {h : ℝ} (hh : 0 < h) (ω : ℕ → ℝ) :
    (∫ z in Ioo (a.val - h) (a.val + h), resistancePhysicalBandErrorVersion A x S a z ω) /
        (2 * resistancePhysicalBandMass A a.val h) =
      resistancePhysicalBandErrorAverage A x S a h ω /
        (2 * resistancePhysicalBandDensityAverage A a.val h) := by
  unfold resistancePhysicalBandErrorAverage resistancePhysicalBandDensityAverage
  have hM := (resistancePhysicalBandMass_pos A a.val hh).ne'
  have hh0 := hh.ne'
  field_simp

end TimeTraps.Probability
