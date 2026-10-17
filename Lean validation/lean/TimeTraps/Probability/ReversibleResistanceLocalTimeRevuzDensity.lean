module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzBound
public import TimeTraps.Probability.ReversibleResistancePhysicalBandMeasurable

@[expose] public section

/-! Integrable occupation-density sections and a uniform mean bound.
The physical density is rho times the fixed-site coefficient; zero outside
the physical interior remains just its density representative convention. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

noncomputable def resistanceRevuzMeanBound (A : IntervalMedium) (S : ℝ≥0) : ℝ :=
  1 + (3 * A.resistanceLength ^ 2 + 6 * S.val + 3 * (S.val / A.resistanceLength) ^ 2)

theorem resistanceRevuzMeanBound_nonneg (A : IntervalMedium) (S : ℝ≥0) :
    0 ≤ resistanceRevuzMeanBound A S := by
  have hS := S.coe_nonneg
  unfold resistanceRevuzMeanBound
  positivity

theorem reversibleResistanceOccupationDensity_level_integrable (A : IntervalMedium) (x z : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => reversibleResistanceOccupationDensity A x T ω z) brownianDyadicMeasure := by
  by_cases hz : z ∈ Ioo A.source.left A.source.right
  · have hi := ((reversibleResistanceLocalTime_memLp_two A x z T).integrable (by norm_num)).const_mul
      (A.source.density z)
    apply hi.congr
    filter_upwards [reversibleResistanceLocalTime_density_normalization A x hz] with ω hω
    exact (hω T).symm
  · simpa only [reversibleResistanceOccupationDensity, indicator_of_notMem hz] using
      (integrable_const (μ := brownianDyadicMeasure) (0 : ℝ))

theorem reversibleResistanceOccupationDensity_mean_bound (A : IntervalMedium) (x z : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) :
    (∫ ω, reversibleResistanceOccupationDensity A x T ω z ∂brownianDyadicMeasure) ≤
      resistancePhysicalDensity A z * resistanceRevuzMeanBound A S := by
  by_cases hz : z ∈ Ioo A.source.left A.source.right
  · have he : (∫ ω, reversibleResistanceOccupationDensity A x T ω z ∂brownianDyadicMeasure) =
        A.source.density z * ∫ ω, reversibleResistanceLocalTime A x z T ω ∂brownianDyadicMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [reversibleResistanceLocalTime_density_normalization A x hz] with ω hω
      exact hω T
    rw [he, resistancePhysicalDensity_eq A (Ioo_subset_Icc_self hz)]
    exact mul_le_mul_of_nonneg_left (reversibleResistanceLocalTime_mean_bound A x z T S hS)
      (A.source.positive z (Ioo_subset_Icc_self hz)).le
  · simp only [reversibleResistanceOccupationDensity, indicator_of_notMem hz, integral_zero]
    exact mul_nonneg (resistancePhysicalDensity_pos A z).le (resistanceRevuzMeanBound_nonneg A S)

theorem reversibleResistanceOccupationDensity_spatial_product_integrable (A : IntervalMedium) (x a h : ℝ)
    (T S : ℝ≥0) (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => reversibleResistanceOccupationDensity A x T p.2 p.1)
      ((volume.restrict (Ioo (a - h) (a + h))).prod brownianDyadicMeasure) := by
  have hm := (reversibleResistanceOccupationDensity_spatial_jointlyMeasurable A x T).aestronglyMeasurable
    (μ := (volume.restrict (Ioo (a - h) (a + h))).prod brownianDyadicMeasure)
  have hd : IntegrableOn (resistancePhysicalDensity A) (Ioo (a - h) (a + h)) volume :=
    (resistancePhysicalDensity_continuous A).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  apply (integrable_prod_iff hm).mpr
  refine ⟨Eventually.of_forall (fun z => reversibleResistanceOccupationDensity_level_integrable A x z T), ?_⟩
  apply (hd.mul_const (resistanceRevuzMeanBound A S)).mono' hm.norm.integral_prod_right'
  filter_upwards [] with z
  simp only [Real.norm_eq_abs, abs_of_nonneg (reversibleResistanceOccupationDensity_nonneg A x T _ z)]
  rw [abs_of_nonneg (integral_nonneg (fun ω => reversibleResistanceOccupationDensity_nonneg A x T ω z))]
  exact reversibleResistanceOccupationDensity_mean_bound A x z T S hS

end TimeTraps.Probability
