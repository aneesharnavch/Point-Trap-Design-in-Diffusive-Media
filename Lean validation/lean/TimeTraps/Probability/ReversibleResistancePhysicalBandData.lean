module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandWindow
public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandParticle

@[expose] public section

/-! Plain physical occupation divided by the band's speed-measure mass.
Projection only extends the denominator outside the state interval; the
source formula is exact whenever the band lies in that interval. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def resistancePhysicalBandMass (A : IntervalMedium) (a h : ℝ) : ℝ :=
  ∫ z in Ioo (a - h) (a + h), resistancePhysicalDensity A z

noncomputable def resistancePhysicalBandDensityAverage (A : IntervalMedium) (a h : ℝ) : ℝ :=
  (1 / (2 * h)) * resistancePhysicalBandMass A a h

noncomputable def reversibleResistancePhysicalOccupationBand (A : IntervalMedium) (x a h : ℝ)
    (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  brownianItoDrift (reversibleResistancePath A x) (brownianBandIndicator a h) T ω /
    resistancePhysicalBandMass A a h

theorem resistancePhysicalBandMass_pos (A : IntervalMedium) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    0 < resistancePhysicalBandMass A a h := by
  unfold resistancePhysicalBandMass
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : a - h ≤ a + h)]
  apply intervalIntegral.integral_pos (by linarith) (resistancePhysicalDensity_continuous A).continuousOn
  · exact fun z _ => (resistancePhysicalDensity_pos A z).le
  · exact ⟨a, ⟨by linarith, by linarith⟩, resistancePhysicalDensity_pos A a⟩

theorem resistancePhysicalBandMass_eq (A : IntervalMedium) (a h : ℝ)
    (hband : Ioo (a - h) (a + h) ⊆ Icc A.source.left A.source.right) :
    resistancePhysicalBandMass A a h = ∫ z in Ioo (a - h) (a + h), A.source.density z := by
  apply setIntegral_congr_fun measurableSet_Ioo
  exact fun z hz => resistancePhysicalDensity_eq A (hband hz)

theorem resistancePhysicalBandDensityAverage_tendsto (A : IntervalMedium) {a : ℝ}
    (ha : a ∈ Icc A.source.left A.source.right) :
    Tendsto (resistancePhysicalBandDensityAverage A a) (𝓝[>] 0) (𝓝 (A.source.density a)) := by
  have ht := continuous_band_average_tendsto (resistancePhysicalDensity_continuous A) a
  rw [resistancePhysicalDensity_eq A ha] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [intervalIntegral.integral_of_le (by linarith [show 0 < h from hh]), integral_Ioc_eq_integral_Ioo]
  rfl

theorem reversibleResistancePhysicalOccupationBand_formula (A : IntervalMedium) (x a h : ℝ)
    (hband : Ioo (a - h) (a + h) ⊆ Icc A.source.left A.source.right)
    (T : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistancePhysicalOccupationBand A x a h T ω =
      (∫ t in (0 : ℝ)..T.val, if |reversibleResistancePath A x t.toNNReal ω - a| < h then (1 : ℝ) else 0) /
        (∫ z in Ioo (a - h) (a + h), A.source.density z) := by
  simp only [reversibleResistancePhysicalOccupationBand, brownianItoDrift, brownianBandIndicator_apply,
    resistancePhysicalBandMass_eq A a h hband]

theorem reversibleResistancePhysicalOccupationBand_particle_measurable (A : IntervalMedium) (x a h : ℝ) (T : ℝ≥0) :
    Measurable[reversibleResistanceParticleSigma A x] (reversibleResistancePhysicalOccupationBand A x a h T) := by
  let : MeasurableSpace (ℕ → ℝ) := reversibleResistanceParticleSigma A x
  exact (brownianItoDrift_bounded_measurable (brownianBandIndicator_measurable a h)
    (reversibleResistancePath_particle_jointlyMeasurable A x) T).div_const _

theorem reversibleResistancePhysicalOccupationBand_spatial_ae (A : IntervalMedium) (x a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (h : ℝ) (T : ℝ≥0),
      IntegrableOn (reversibleResistanceOccupationDensity A x T ω) (Ioo (a - h) (a + h)) volume ∧
      reversibleResistancePhysicalOccupationBand A x a h T ω =
        (∫ z in Ioo (a - h) (a + h), reversibleResistanceOccupationDensity A x T ω z) /
          resistancePhysicalBandMass A a h := by
  filter_upwards [reversibleResistanceOccupationDensity_bounded_occupation A x] with ω hω h T
  have ho := hω (brownianBandIndicator a h) (brownianBandIndicator_measurable a h)
    1 (brownianBandIndicator_abs_le_one a h) T
  have he : (fun z => brownianBandIndicator a h z * reversibleResistanceOccupationDensity A x T ω z) =
      (Ioo (a - h) (a + h)).indicator (reversibleResistanceOccupationDensity A x T ω) := by
    funext z
    by_cases hz : z ∈ Ioo (a - h) (a + h)
    · simp only [brownianBandIndicator, indicator_of_mem hz, one_mul]
    · simp only [brownianBandIndicator, indicator_of_notMem hz, zero_mul]
  rw [he] at ho
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).mp ho.1, ?_⟩
  rw [integral_indicator measurableSet_Ioo] at ho
  exact congrArg (fun r : ℝ => r / resistancePhysicalBandMass A a h) ho.2.2.symm

end TimeTraps.Probability
