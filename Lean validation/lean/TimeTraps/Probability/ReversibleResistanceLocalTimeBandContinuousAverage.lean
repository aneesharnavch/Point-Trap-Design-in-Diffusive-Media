module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandData
public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentWindow

@[expose] public section

/-! Genuine speed-mass weighted averages of a continuous Banach-valued
reference field. Their normalization is the original physical speed mass;
only continuous positive coefficients enter the limit. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def resistancePhysicalWeightedAverage (A : IntervalMedium)
    (V : ℝ → E) (a h : ℝ) : E :=
  (resistancePhysicalBandMass A a h)⁻¹ • ∫ z in (a - h)..(a + h),
    resistancePhysicalDensity A z • V (resistancePhysicalCoordinate A z)

omit [CompleteSpace E] in
theorem resistancePhysicalWeightedIntegrand_continuous (A : IntervalMedium)
    {V : ℝ → E} (hV : Continuous V) :
    Continuous (fun z => resistancePhysicalDensity A z • V (resistancePhysicalCoordinate A z)) :=
  (resistancePhysicalDensity_continuous A).smul
    (hV.comp (resistancePhysicalCoordinate_continuous A))

theorem resistancePhysicalWeightedAverage_tendsto (A : IntervalMedium)
    {V : ℝ → E} (hV : Continuous V) {a : ℝ}
    (ha : a ∈ Icc A.source.left A.source.right) :
    Tendsto (resistancePhysicalWeightedAverage A V a) (𝓝[>] 0) (𝓝 (V (A.resistance a))) := by
  have hn := continuous_band_average_tendsto (resistancePhysicalWeightedIntegrand_continuous A hV) a
  have hd := (resistancePhysicalBandDensityAverage_tendsto A ha).inv₀ (A.source.positive a ha).ne'
  have ht := hd.smul hn
  rw [resistancePhysicalDensity_eq A ha, resistancePhysicalCoordinate_eq A ha,
    inv_smul_smul₀ (A.source.positive a ha).ne'] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change ((1 / (2 * h) * resistancePhysicalBandMass A a h)⁻¹) •
    ((1 / (2 * h)) • _) = (resistancePhysicalBandMass A a h)⁻¹ • _
  rw [smul_smul]
  congr 1
  have hp := resistancePhysicalBandMass_pos A a (show 0 < h from hh)
  field_simp
  exact div_self (ne_of_gt (show 0 < h from hh))

end TimeTraps.Probability
