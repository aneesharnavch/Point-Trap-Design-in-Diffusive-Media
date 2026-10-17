module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandErrorAverage
public import TimeTraps.Probability.ReversibleResistancePhysicalBandMeasurable
public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimePaths

@[expose] public section

/-! The actual physical occupation density has a jointly measurable
spatial error bound at the random inverse horizon. Fixed levels use the
common all-time local-time event before the Fubini exchange. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem resistancePhysicalBand_level_bound_ae (A : IntervalMedium) (x : ℝ) (S T : ℝ≥0)
    (a : Ioo A.source.left A.source.right)
    (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S) {z : ℝ}
    (hz : z ∈ Ioo A.source.left A.source.right)
    (hzR : A.resistance z ∈ Ioo (A.resistance a / 2) ((A.resistance a + A.resistanceLength) / 2)) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      |reversibleResistanceOccupationDensity A x T ω z -
        resistancePhysicalDensity A z * reversibleResistanceLocalTime A x a.val T ω| ≤
      resistancePhysicalBandErrorVersion A x S a z ω / 2 := by
  let ar : Ioo (0 : ℝ) A.resistanceLength := ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩
  have hσ : 0 < Real.sqrt (2 * (1 : ℝ)) := Real.sqrt_pos.mpr (by norm_num)
  have hc := reflectedBandClippedLevel_eq ar (Ioo_subset_Icc_self hzR)
  filter_upwards [reflectedBandErrorVersion_bound_ae A.resistanceLength A.resistanceLength_pos
    (A.resistance x) hσ S ar (A.resistance z),
    reversibleResistanceLocalTime_density_normalization A x hz] with ω hM hd
  have hm := hM (reversibleResistanceInversePath A x T ω) (hS ω)
  rw [hc] at hm
  have hdiff : |reversibleResistanceLocalTime A x z T ω - reversibleResistanceLocalTime A x a.val T ω| ≤
      reflectedBandErrorVersion A.resistanceLength A.resistanceLength_pos (A.resistance x) hσ S ar (A.resistance z) ω / 2 := by
    unfold reversibleResistanceLocalTime reflectedInteriorOccupationCoefficient
    rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hσ)]
    have hsq : (Real.sqrt (2 * (1 : ℝ))) ^ 2 = 2 := by norm_num
    rw [hsq]
    exact div_le_div_of_nonneg_right hm (by norm_num)
  rw [hd T, resistancePhysicalDensity_eq A (Ioo_subset_Icc_self hz), ← mul_sub, abs_mul,
    abs_of_pos (A.source.positive z (Ioo_subset_Icc_self hz))]
  unfold resistancePhysicalBandErrorVersion
  rw [resistancePhysicalDensity_eq A (Ioo_subset_Icc_self hz), resistancePhysicalCoordinate_eq A (Ioo_subset_Icc_self hz),
    mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hdiff (A.source.positive z (Ioo_subset_Icc_self hz)).le

theorem resistancePhysicalBand_spatial_bound_ae (A : IntervalMedium) (x : ℝ) (S T : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (h : ℝ)
    (hS : ∀ ω, reversibleResistanceInversePath A x T ω ≤ S)
    (hband : ∀ z ∈ Ioo (a.val - h) (a.val + h), z ∈ Ioo A.source.left A.source.right ∧
      A.resistance z ∈ Ioo (A.resistance a / 2) ((A.resistance a + A.resistanceLength) / 2)) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ᵐ z ∂volume.restrict (Ioo (a.val - h) (a.val + h)),
      |reversibleResistanceOccupationDensity A x T ω z -
        resistancePhysicalDensity A z * reversibleResistanceLocalTime A x a.val T ω| ≤
      resistancePhysicalBandErrorVersion A x S a z ω / 2 := by
  let q : ℝ × (ℕ → ℝ) → ℝ≥0 × (ℕ → ℝ) := fun p => (T, p.2)
  have hq : Measurable q := measurable_const.prodMk measurable_snd
  have hcenter := (reversibleResistanceLocalTime_jointlyMeasurable A x a.val).comp hq
  dsimp only [Function.comp_def, q] at hcenter
  have hm : MeasurableSet {p : ℝ × (ℕ → ℝ) |
      |reversibleResistanceOccupationDensity A x T p.2 p.1 -
        resistancePhysicalDensity A p.1 * reversibleResistanceLocalTime A x a.val T p.2| ≤
      resistancePhysicalBandErrorVersion A x S a p.1 p.2 / 2} :=
    measurableSet_le ((reversibleResistanceOccupationDensity_spatial_jointlyMeasurable A x T).sub
      (((resistancePhysicalDensity_continuous A).measurable.comp measurable_fst).mul hcenter)).abs
      ((resistancePhysicalBandErrorVersion_jointlyMeasurable A x S a).div_const 2)
  apply (Measure.ae_ae_comm hm).mp
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with z hz
  exact resistancePhysicalBand_level_bound_ae A x S T a hS (hband z hz).1 (hband z hz).2

end TimeTraps.Probability
