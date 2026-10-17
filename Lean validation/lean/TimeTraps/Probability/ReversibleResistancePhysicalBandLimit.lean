module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandMoments
public import TimeTraps.Probability.ReflectedLocalTimeBandSubsequence

@[expose] public section

/-! The paper's original speed-mass-normalized shrinking physical bands
converge to the transported fixed-site local time in mean square. An
almost-everywhere convergent band sequence follows; full sample spatial
continuity and an almost-sure limit over every radius are not assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem resistancePhysicalBand_small_eventually (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h ∧ ∀ z ∈ Ioo (a.val - h) (a.val + h),
      z ∈ Ioo A.source.left A.source.right ∧
      A.resistance z ∈ Ioo (A.resistance a / 2) ((A.resistance a + A.resistanceLength) / 2) := by
  obtain ⟨r, hr, hw⟩ := reversibleResistancePhysicalBand_window A a.property
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with h hh hs
  refine ⟨hh, fun z hz => hw z ?_⟩
  rw [abs_lt]
  constructor <;> linarith [hz.1, hz.2, show h < r from hs]

theorem reversibleResistancePhysicalOccupationBand_square_tendsto (A : IntervalMedium) (x : ℝ)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) :
    Tendsto (fun h => ∫ ω, (reversibleResistancePhysicalOccupationBand A x a.val h T ω -
      reversibleResistanceLocalTime A x a.val T ω) ^ 2 ∂brownianDyadicMeasure) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  apply squeeze_zero' (Eventually.of_forall (fun h => integral_nonneg (fun ω => sq_nonneg _)))
  · filter_upwards [resistancePhysicalBand_small_eventually A a] with h hh
    exact resistancePhysicalBand_error_secondMoment_le A x S T a hh.1 hS hh.2
  · have hden := ((resistancePhysicalBandDensityAverage_tendsto A (Ioo_subset_Icc_self a.property)).const_mul (2 : ℝ)).pow 2
    have hlim := (resistancePhysicalBandErrorAverage_square_tendsto A x S a).div hden
      (show (2 * A.source.density a.val) ^ 2 ≠ 0 by
        have hp := A.source.positive a.val (Ioo_subset_Icc_self a.property)
        positivity)
    change Tendsto (fun h =>
      (∫ ω, resistancePhysicalBandErrorAverage A x S a h ω ^ 2 ∂brownianDyadicMeasure) /
        (2 * resistancePhysicalBandDensityAverage A a.val h) ^ 2)
      (𝓝[>] 0) (𝓝 (0 / (2 * A.source.density a.val) ^ 2)) at hlim
    simpa only [zero_div] using hlim

theorem reversibleResistance_physical_speedMass_band_square_tendsto (A : IntervalMedium) (x : ℝ)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) :
    Tendsto (fun h => ∫ ω,
      ((∫ t in (0 : ℝ)..T.val,
        if |reversibleResistancePath A x t.toNNReal ω - a.val| < h then (1 : ℝ) else 0) /
          (∫ z in Ioo (a.val - h) (a.val + h), A.source.density z) -
        reversibleResistanceLocalTime A x a.val T ω) ^ 2 ∂brownianDyadicMeasure) (𝓝[>] 0) (𝓝 0) := by
  apply (reversibleResistancePhysicalOccupationBand_square_tendsto A x a T).congr'
  filter_upwards [resistancePhysicalBand_small_eventually A a] with h hh
  apply integral_congr_ae
  filter_upwards with ω
  rw [reversibleResistancePhysicalOccupationBand_formula A x a.val h
    (fun z hz => Ioo_subset_Icc_self (hh.2 z hz).1) T ω]

theorem reversibleResistancePhysicalOccupationBand_sequence (A : IntervalMedium) (x : ℝ)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) :
    ∃ u : ℕ → ℝ, (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) ∧ ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n => reversibleResistancePhysicalOccupationBand A x a.val (u n) T ω) atTop
        (𝓝 (reversibleResistanceLocalTime A x a.val T ω)) := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  obtain ⟨r, hr, hw⟩ := reversibleResistancePhysicalBand_window A a.property
  have hmem (h : ℝ) (hh : 0 < h) (hs : h < r) :=
    resistancePhysicalBand_error_memLp A x S T a hh hS (fun z hz => hw z (by
      rw [abs_lt]
      constructor <;> linarith [hz.1, hz.2]))
  obtain ⟨u, hu, ht, hAE⟩ := occupationBand_exists_sequence_tendsto_ae hr hmem
    (reversibleResistancePhysicalOccupationBand_square_tendsto A x a T)
  exact ⟨u, fun n => (hu n).1, ht, hAE⟩

theorem reversibleResistance_physical_speedMass_band_sequence (A : IntervalMedium) (x : ℝ)
    (a : Ioo A.source.left A.source.right) (T : ℝ≥0) :
    ∃ u : ℕ → ℝ, (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) ∧ ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n =>
        (∫ t in (0 : ℝ)..T.val,
          if |reversibleResistancePath A x t.toNNReal ω - a.val| < u n then (1 : ℝ) else 0) /
            (∫ z in Ioo (a.val - u n) (a.val + u n), A.source.density z)) atTop
        (𝓝 (reversibleResistanceLocalTime A x a.val T ω)) := by
  obtain ⟨u, hu, ht, hAE⟩ := reversibleResistancePhysicalOccupationBand_sequence A x a T
  have ht' : Tendsto u atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨ht, Eventually.of_forall hu⟩
  have hs := ht'.eventually (resistancePhysicalBand_small_eventually A a)
  refine ⟨u, hu, ht, ?_⟩
  filter_upwards [hAE] with ω hω
  apply hω.congr'
  filter_upwards [hs] with n hn
  exact reversibleResistancePhysicalOccupationBand_formula A x a.val (u n)
    (fun z hz => Ioo_subset_Icc_self (hn.2 z hz).1) T ω

end TimeTraps.Probability
