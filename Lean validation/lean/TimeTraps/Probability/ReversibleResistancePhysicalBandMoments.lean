module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandBound
public import TimeTraps.Probability.ReversibleResistancePhysicalBandEstimate

@[expose] public section

/-! Mean-square control of the genuine physical occupation bands by the
weighted spatial maximal error divided by the exact speed-mass average. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem resistancePhysicalBand_error_bound_ae (A : IntervalMedium) (x : ℝ) (S T : ℝ≥0)
    (a : Ioo A.source.left A.source.right) {h : ℝ} (hh : 0 < h)
    (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (hband : ∀ z ∈ Ioo (a.val - h) (a.val + h), z ∈ Ioo A.source.left A.source.right ∧
      A.resistance z ∈ Ioo (A.resistance a / 2) ((A.resistance a + A.resistanceLength) / 2)) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      |reversibleResistancePhysicalOccupationBand A x a.val h T ω - reversibleResistanceLocalTime A x a.val T ω| ≤
      resistancePhysicalBandErrorAverage A x S a h ω / (2 * resistancePhysicalBandDensityAverage A a.val h) := by
  filter_upwards [reversibleResistancePhysicalOccupationBand_spatial_ae A x a.val,
    resistancePhysicalBandErrorVersion_spatial_integrable_ae A x S a h,
    resistancePhysicalBand_spatial_bound_ae A x S T a h hS hband] with ω hF hE hb
  rw [(hF h T).2]
  have hρ : IntegrableOn (resistancePhysicalDensity A) (Ioo (a.val - h) (a.val + h)) volume :=
    (resistancePhysicalDensity_continuous A).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  exact (speedMass_average_error_bound (reversibleResistanceLocalTime A x a.val T ω)
    (hF h T).1 hρ hE (resistancePhysicalBandMass_pos A a.val hh) hb).trans_eq
      (resistancePhysicalBand_average_error_ratio A x S a hh ω)

theorem resistancePhysicalBand_error_memLp (A : IntervalMedium) (x : ℝ) (S T : ℝ≥0)
    (a : Ioo A.source.left A.source.right) {h : ℝ} (hh : 0 < h)
    (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (hband : ∀ z ∈ Ioo (a.val - h) (a.val + h), z ∈ Ioo A.source.left A.source.right ∧
      A.resistance z ∈ Ioo (A.resistance a / 2) ((A.resistance a + A.resistanceLength) / 2)) :
    MemLp (fun ω => reversibleResistancePhysicalOccupationBand A x a.val h T ω -
      reversibleResistanceLocalTime A x a.val T ω) 2 brownianDyadicMeasure := by
  have hB : Measurable (reversibleResistancePhysicalOccupationBand A x a.val h T) :=
    (reversibleResistancePhysicalOccupationBand_particle_measurable A x a.val h T).mono
      (reversibleResistanceParticleSigma_le A x) le_rfl
  let q : (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) := fun ω => (T, ω)
  have hq : Measurable q := measurable_const.prodMk measurable_id
  have hL := (reversibleResistanceLocalTime_jointlyMeasurable A x a.val).comp hq
  dsimp only [Function.comp_def, q] at hL
  have hM : MemLp (fun ω => resistancePhysicalBandErrorAverage A x S a h ω /
      (2 * resistancePhysicalBandDensityAverage A a.val h)) 2 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using (resistancePhysicalBandErrorAverage_memLp A x S a h).mul_const
      (2 * resistancePhysicalBandDensityAverage A a.val h)⁻¹
  exact hM.mono' (hB.sub hL).aestronglyMeasurable
    (resistancePhysicalBand_error_bound_ae A x S T a hh hS hband)

theorem resistancePhysicalBand_error_secondMoment_le (A : IntervalMedium) (x : ℝ) (S T : ℝ≥0)
    (a : Ioo A.source.left A.source.right) {h : ℝ} (hh : 0 < h)
    (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (hband : ∀ z ∈ Ioo (a.val - h) (a.val + h), z ∈ Ioo A.source.left A.source.right ∧
      A.resistance z ∈ Ioo (A.resistance a / 2) ((A.resistance a + A.resistanceLength) / 2)) :
    (∫ ω, (reversibleResistancePhysicalOccupationBand A x a.val h T ω -
      reversibleResistanceLocalTime A x a.val T ω) ^ 2 ∂brownianDyadicMeasure) ≤
    (∫ ω, resistancePhysicalBandErrorAverage A x S a h ω ^ 2 ∂brownianDyadicMeasure) /
      (2 * resistancePhysicalBandDensityAverage A a.val h) ^ 2 := by
  have hM : MemLp (fun ω => resistancePhysicalBandErrorAverage A x S a h ω /
      (2 * resistancePhysicalBandDensityAverage A a.val h)) 2 brownianDyadicMeasure := by
    simpa only [div_eq_mul_inv] using (resistancePhysicalBandErrorAverage_memLp A x S a h).mul_const
      (2 * resistancePhysicalBandDensityAverage A a.val h)⁻¹
  calc
    _ ≤ ∫ ω, (resistancePhysicalBandErrorAverage A x S a h ω /
        (2 * resistancePhysicalBandDensityAverage A a.val h)) ^ 2 ∂brownianDyadicMeasure := by
      apply integral_mono_ae (resistancePhysicalBand_error_memLp A x S T a hh hS hband).integrable_sq hM.integrable_sq
      filter_upwards [resistancePhysicalBand_error_bound_ae A x S T a hh hS hband] with ω hb
      have hs := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hb)).mpr hb
      simpa only [sq_abs] using hs
    _ = _ := by simp only [div_eq_mul_inv, mul_pow, inv_pow, integral_mul_const]

end TimeTraps.Probability
