module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandError

@[expose] public section

/-! Physical spatial averages of the weighted maximal error are genuine
square-integrable random variables. Product integrability is derived from
the continuous L2 family before using Fubini. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

noncomputable def resistancePhysicalBandErrorAverage (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (h : ℝ) (ω : ℕ → ℝ) : ℝ :=
  (1 / (2 * h)) * ∫ z in Ioo (a.val - h) (a.val + h), resistancePhysicalBandErrorVersion A x S a z ω

noncomputable def resistancePhysicalBandErrorAverageL2 (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (h : ℝ) : Lp ℝ 2 brownianDyadicMeasure :=
  (1 / (2 * h)) • ∫ z in Ioo (a.val - h) (a.val + h), resistancePhysicalBandErrorL2 A x S a z

theorem resistancePhysicalBandErrorL2_integrableOn (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (h : ℝ) :
    IntegrableOn (resistancePhysicalBandErrorL2 A x S a) (Ioo (a.val - h) (a.val + h)) volume :=
  (resistancePhysicalBandErrorL2_continuous A x S a).integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem resistancePhysicalBandErrorVersion_product_integrable (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (h : ℝ) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => resistancePhysicalBandErrorVersion A x S a p.1 p.2)
      ((volume.restrict (Ioo (a.val - h) (a.val + h))).prod brownianDyadicMeasure) :=
  real_L2_sections_integrable (resistancePhysicalBandErrorL2_integrableOn A x S a h)
    (resistancePhysicalBandErrorVersion_jointlyMeasurable A x S a).aestronglyMeasurable
    (fun z => (resistancePhysicalBandErrorVersion_ae A x S a z).symm)

theorem resistancePhysicalBandErrorVersion_spatial_integrable_ae (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (h : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, IntegrableOn (fun z => resistancePhysicalBandErrorVersion A x S a z ω)
      (Ioo (a.val - h) (a.val + h)) volume :=
  (resistancePhysicalBandErrorVersion_product_integrable A x S a h).prod_left_ae

theorem resistancePhysicalBandErrorAverageL2_coe (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (h : ℝ) :
    resistancePhysicalBandErrorAverageL2 A x S a h =ᵐ[brownianDyadicMeasure]
      resistancePhysicalBandErrorAverage A x S a h := by
  have hi := real_L2_integral_sections_ae (resistancePhysicalBandErrorL2_integrableOn A x S a h)
    (resistancePhysicalBandErrorVersion_jointlyMeasurable A x S a).aestronglyMeasurable
    (fun z => (resistancePhysicalBandErrorVersion_ae A x S a z).symm)
  filter_upwards [Lp.coeFn_smul (1 / (2 * h))
    (∫ z in Ioo (a.val - h) (a.val + h), resistancePhysicalBandErrorL2 A x S a z), hi] with ω hs hω
  change ((1 / (2 * h)) • (∫ z in Ioo (a.val - h) (a.val + h),
    resistancePhysicalBandErrorL2 A x S a z : Lp ℝ 2 brownianDyadicMeasure)) ω = _
  rw [hs, Pi.smul_apply, smul_eq_mul, hω]
  rfl

theorem resistancePhysicalBandErrorAverage_memLp (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (h : ℝ) :
    MemLp (resistancePhysicalBandErrorAverage A x S a h) 2 brownianDyadicMeasure :=
  MemLp.ae_eq (resistancePhysicalBandErrorAverageL2_coe A x S a h)
    (Lp.memLp (resistancePhysicalBandErrorAverageL2 A x S a h))

theorem resistancePhysicalBandErrorAverageL2_tendsto (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) :
    Tendsto (resistancePhysicalBandErrorAverageL2 A x S a) (𝓝[>] 0) (𝓝 0) := by
  have ht := continuous_band_average_tendsto (resistancePhysicalBandErrorL2_continuous A x S a) a.val
  rw [resistancePhysicalBandErrorL2_center] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [intervalIntegral.integral_of_le (by linarith [show 0 < h from hh]), integral_Ioc_eq_integral_Ioo]
  rfl

theorem resistancePhysicalBandErrorAverage_square_tendsto (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) :
    Tendsto (fun h => ∫ ω, resistancePhysicalBandErrorAverage A x S a h ω ^ 2 ∂brownianDyadicMeasure)
      (𝓝[>] 0) (𝓝 0) := by
  have he (h : ℝ) : (∫ ω, resistancePhysicalBandErrorAverage A x S a h ω ^ 2 ∂brownianDyadicMeasure) =
      ‖resistancePhysicalBandErrorAverageL2 A x S a h‖ ^ 2 := by
    rw [← memLp_norm_toLp_sq (resistancePhysicalBandErrorAverage_memLp A x S a h)]
    congr 2
    apply Lp.ext
    exact (resistancePhysicalBandErrorAverage_memLp A x S a h).coeFn_toLp.trans
      (resistancePhysicalBandErrorAverageL2_coe A x S a h).symm
  simpa only [he, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (resistancePhysicalBandErrorAverageL2_tendsto A x S a).norm.pow 2

end TimeTraps.Probability
