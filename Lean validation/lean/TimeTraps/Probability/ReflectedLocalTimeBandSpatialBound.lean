module

public import TimeTraps.Probability.ReflectedLocalTimeBandData
public import TimeTraps.Probability.ReflectedLocalTimeBandErrorVersion
public import TimeTraps.Probability.ReflectedInteriorOccupationMeasurable

@[expose] public section

/-! Product measurability transports the fixed-level maximal estimate
to almost every spatial point on each sample. Only a fixed deterministic
time is used here; the compact-time result will use a countable dense set. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedOccupationDensity_band_level_bound_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h b : ℝ}
    (hh : h < min (a.val / 2) ((L - a.val) / 2)) (hb : b ∈ Ioo (a.val - h) (a.val + h)) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |foldedOccupationDensity L D x t ω b -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω| ≤
      reflectedBandErrorVersion L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a b ω /
        (Real.sqrt (2 * D)) ^ 2 := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hc := reflectedBandClippedLevel_eq_on_band a hh hb
  have hbI : b ∈ Ioo (0 : ℝ) L := hc ▸ (reflectedBandClippedLevel a b).property
  filter_upwards [reflectedBandErrorVersion_bound_ae L hL x hσ T a b,
    reflectedInteriorOccupationCoefficient_density_all_times_ae L hL D hD x b hbI] with ω hM hden t ht
  rw [← hden t, reflectedInteriorOccupationCoefficient, reflectedInteriorOccupationCoefficient,
    ← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hσ)]
  have hm := hM t ht
  rw [hc] at hm
  exact div_le_div_of_nonneg_right hm (sq_nonneg _)

theorem reflectedOccupationDensity_band_spatial_bound_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ}
    (hh : h < min (a.val / 2) ((L - a.val) / 2)) (t : ℝ≥0) (ht : t ≤ T) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ᵐ b ∂volume.restrict (Ioo (a.val - h) (a.val + h)),
      |foldedOccupationDensity L D x t ω b -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t ω| ≤
      reflectedBandErrorVersion L hL x (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T a b ω /
        (Real.sqrt (2 * D)) ^ 2 := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  let q : ℝ × (ℕ → ℝ) → ℝ × (ℕ → ℝ) := fun p => (a.val, p.2)
  have hq : Measurable q := measurable_const.prodMk measurable_snd
  have hcenter' := (reflectedInteriorOccupationCoefficient_jointlyMeasurable x (Real.sqrt (2 * D)) L t).comp hq
  dsimp only [Function.comp_def, q] at hcenter'
  have hcenter : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t p.2) := hcenter'
  have hm : MeasurableSet {p : ℝ × (ℕ → ℝ) |
      |foldedOccupationDensity L D x t p.2 p.1 -
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t p.2| ≤
      reflectedBandErrorVersion L hL x hσ T a p.1 p.2 / (Real.sqrt (2 * D)) ^ 2} :=
    measurableSet_le ((foldedOccupationDensity_timeSlice_jointlyMeasurable L D x t).sub hcenter).abs
      ((reflectedBandErrorVersion_jointlyMeasurable L hL x hσ T a).div_const _)
  apply (Measure.ae_ae_comm hm).mp
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with b hb
  exact (reflectedOccupationDensity_band_level_bound_ae L hL D hD x T a hh hb).mono
    (fun ω hω => hω t ht)

end TimeTraps.Probability
