module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandContinuousAverage
public import TimeTraps.Probability.ReversibleResistancePairingData

@[expose] public section

/-! Speed-mass averages of a continuous physical field. The spatial
cutoff remains the literal open band and the denominator is its actual
speed mass; the conclusion holds at every interior site. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def resistanceRevuzFieldExtension (A : IntervalMedium)
    (q : C(Icc A.source.left A.source.right, ℝ)) (z : ℝ) : ℝ :=
  q (projIcc A.source.left A.source.right A.source.increasing.le z)

theorem resistanceRevuzFieldExtension_continuous (A : IntervalMedium)
    (q : C(Icc A.source.left A.source.right, ℝ)) :
    Continuous (resistanceRevuzFieldExtension A q) := q.continuous.comp continuous_projIcc

theorem resistanceRevuzFieldExtension_eq (A : IntervalMedium)
    (q : C(Icc A.source.left A.source.right, ℝ)) (z : Icc A.source.left A.source.right) :
    resistanceRevuzFieldExtension A q z.val = q z := by
  simp only [resistanceRevuzFieldExtension, projIcc_of_mem A.source.increasing.le z.property]

theorem resistanceRevuzField_band_integral (A : IntervalMedium) (a h : ℝ)
    (hband : Ioo (a - h) (a + h) ⊆ Ioo A.source.left A.source.right) (q : ℝ → ℝ) :
    (∫ z in A.source.left..A.source.right, A.source.density z * brownianBandIndicator a h z * q z) =
      ∫ z in Ioo (a - h) (a + h), A.source.density z * q z := by
  rw [intervalIntegral.integral_of_le A.source.increasing.le, integral_Ioc_eq_integral_Ioo,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have hn : z ∉ Ioo (a - h) (a + h) := fun h => hz (hband h)
      simp only [brownianBandIndicator, indicator_of_notMem hn, mul_zero, zero_mul])]
  have he : (fun z => A.source.density z * brownianBandIndicator a h z * q z) =
      (Ioo (a - h) (a + h)).indicator (fun z => A.source.density z * q z) := by
    funext z
    by_cases hz : z ∈ Ioo (a - h) (a + h)
    · simp only [brownianBandIndicator, indicator_of_mem hz, mul_one]
    · simp only [brownianBandIndicator, indicator_of_notMem hz, mul_zero, zero_mul]
  rw [he, integral_indicator measurableSet_Ioo]

theorem resistanceRevuzField_average_tendsto (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) (q : C(Icc A.source.left A.source.right, ℝ)) :
    Tendsto (fun h : ℝ =>
      (∫ x, A.source.density x.val * brownianBandIndicator a.val h x.val * q x
        ∂reversibleResistanceLengthMeasure A) / resistancePhysicalBandMass A a.val h)
      (𝓝[>] 0) (𝓝 (q ⟨a.val, Ioo_subset_Icc_self a.property⟩)) := by
  let Q := resistanceRevuzFieldExtension A q
  have hQ := resistanceRevuzFieldExtension_continuous A q
  have hn := continuous_band_average_tendsto ((resistancePhysicalDensity_continuous A).mul hQ) a.val
  have hd := resistancePhysicalBandDensityAverage_tendsto A (Ioo_subset_Icc_self a.property)
  have ht := hn.div hd (A.source.positive a.val (Ioo_subset_Icc_self a.property)).ne'
  simp only [Pi.mul_apply, smul_eq_mul] at ht
  rw [resistancePhysicalDensity_eq A (Ioo_subset_Icc_self a.property),
    mul_div_cancel_left₀ _ (A.source.positive a.val (Ioo_subset_Icc_self a.property)).ne'] at ht
  change Tendsto _ _ (𝓝 (Q a.val)) at ht
  have heQ : Q a.val = q ⟨a.val, Ioo_subset_Icc_self a.property⟩ :=
    resistanceRevuzFieldExtension_eq A q ⟨a.val, Ioo_subset_Icc_self a.property⟩
  rw [heQ] at ht
  obtain ⟨r, hr, hwindow⟩ := reversibleResistancePhysicalBand_window A a.property
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with h hh hhr
  have hband : Ioo (a.val - h) (a.val + h) ⊆ Ioo A.source.left A.source.right := by
    intro z hz
    exact (hwindow z ((abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩).trans hhr)).1
  have hs : (∫ x, A.source.density x.val * brownianBandIndicator a.val h x.val * q x
      ∂reversibleResistanceLengthMeasure A) =
      ∫ z in Ioo (a.val - h) (a.val + h), resistancePhysicalDensity A z * Q z := by
    calc
      _ = ∫ x, A.source.density x.val * brownianBandIndicator a.val h x.val * Q x.val
          ∂reversibleResistanceLengthMeasure A := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => congrArg
          (fun v : ℝ => A.source.density x.val * brownianBandIndicator a.val h x.val * v)
          (resistanceRevuzFieldExtension_eq A q x).symm)
      _ = ∫ z in A.source.left..A.source.right,
          A.source.density z * brownianBandIndicator a.val h z * Q z :=
        reversibleResistanceLengthMeasure_integral A (fun z =>
          A.source.density z * brownianBandIndicator a.val h z * Q z)
      _ = ∫ z in Ioo (a.val - h) (a.val + h), A.source.density z * Q z :=
        resistanceRevuzField_band_integral A a.val h hband Q
      _ = _ := setIntegral_congr_fun measurableSet_Ioo (fun z hz => by
        rw [resistancePhysicalDensity_eq A (Ioo_subset_Icc_self (hband hz))])
  change ((1 / (2 * h)) * (∫ z in (a.val - h)..(a.val + h),
    resistancePhysicalDensity A z * Q z)) / resistancePhysicalBandDensityAverage A a.val h = _
  rw [intervalIntegral.integral_of_le (by linarith [show 0 < h from hh]),
    integral_Ioc_eq_integral_Ioo, ← hs]
  change ((1 / (2 * h)) * _) / ((1 / (2 * h)) * resistancePhysicalBandMass A a.val h) = _
  have hp : 0 < h := hh
  exact mul_div_mul_left _ _ (by positivity : (1 / (2 * h) : ℝ) ≠ 0)

end TimeTraps.Probability
