module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzDensity
public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzBandMean

@[expose] public section

/-! Fubini for genuine physical band means and a bound independent of the
band radius, its center, and the initial state once the common clock cap is
chosen. This bound permits later integration over initial speed measure. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistancePhysicalOccupationBand_mean_spatial (A : IntervalMedium) (x a h : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) :
    (∫ ω, reversibleResistancePhysicalOccupationBand A x a h T ω ∂brownianDyadicMeasure) =
      (∫ z in Ioo (a - h) (a + h),
        ∫ ω, reversibleResistanceOccupationDensity A x T ω z ∂brownianDyadicMeasure) /
          resistancePhysicalBandMass A a h := by
  have hi := reversibleResistanceOccupationDensity_spatial_product_integrable A x a h T S hS
  calc
    _ = (∫ ω, (∫ z in Ioo (a - h) (a + h), reversibleResistanceOccupationDensity A x T ω z)
        ∂brownianDyadicMeasure) / resistancePhysicalBandMass A a h := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [reversibleResistancePhysicalOccupationBand_spatial_ae A x a] with ω hω
      exact (hω h T).2
    _ = _ := congrArg (fun v : ℝ => v / resistancePhysicalBandMass A a h)
      (integral_integral_swap hi).symm

theorem reversibleResistancePhysicalOccupationBand_mean_nonneg (A : IntervalMedium) (x a : ℝ)
    {h : ℝ} (hh : 0 < h) (T : ℝ≥0) :
    0 ≤ ∫ ω, reversibleResistancePhysicalOccupationBand A x a h T ω ∂brownianDyadicMeasure := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  rw [reversibleResistancePhysicalOccupationBand_mean_spatial A x a h T S hS]
  exact div_nonneg (integral_nonneg (fun z => integral_nonneg
    (fun ω => reversibleResistanceOccupationDensity_nonneg A x T ω z)))
      (resistancePhysicalBandMass_pos A a hh).le

theorem reversibleResistancePhysicalOccupationBand_mean_bound (A : IntervalMedium) (x a : ℝ)
    {h : ℝ} (hh : 0 < h) (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) :
    (∫ ω, reversibleResistancePhysicalOccupationBand A x a h T ω ∂brownianDyadicMeasure) ≤
      resistanceRevuzMeanBound A S := by
  have hi := reversibleResistanceOccupationDensity_spatial_product_integrable A x a h T S hS
  have hd : IntegrableOn (resistancePhysicalDensity A) (Ioo (a - h) (a + h)) volume :=
    (resistancePhysicalDensity_continuous A).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [reversibleResistancePhysicalOccupationBand_mean_spatial A x a h T S hS]
  have hb : (∫ z in Ioo (a - h) (a + h),
      ∫ ω, reversibleResistanceOccupationDensity A x T ω z ∂brownianDyadicMeasure) ≤
        resistancePhysicalBandMass A a h * resistanceRevuzMeanBound A S := by
    calc
      _ ≤ ∫ z in Ioo (a - h) (a + h), resistancePhysicalDensity A z * resistanceRevuzMeanBound A S := by
        apply integral_mono hi.integral_prod_left (hd.mul_const _)
        exact fun z => reversibleResistanceOccupationDensity_mean_bound A x z T S hS
      _ = _ := integral_mul_const _ _
  exact (div_le_iff₀ (resistancePhysicalBandMass_pos A a hh)).mpr (by simpa only [mul_comm] using hb)

end TimeTraps.Probability
