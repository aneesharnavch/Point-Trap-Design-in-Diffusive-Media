module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandContinuousOccupation

@[expose] public section

/-! The source's plain physical occupation divided by the band's speed
mass converges almost surely for the full positive-radius filter, uniformly
on each compact physical-time horizon. All random inverse times are
evaluated inside a single already simultaneous reference-time event. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistancePhysicalOccupationBand_compact_uniform_as
    (A : IntervalMedium) (x : ℝ) {a : ℝ}
    (ha : a ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime T,
        |reversibleResistancePhysicalOccupationBand A x a h t.val ω -
          reversibleResistanceLocalTime A x a t.val ω|) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  have haR := reversibleResistance_site_interior A ha
  let l := A.resistance a / 2
  let r := (A.resistance a + A.resistanceLength) / 2
  have hl : 0 < l := by dsimp only [l]; linarith [haR.1]
  have hlr : l ≤ r := by dsimp only [l, r]; linarith [A.resistanceLength_pos]
  have hr : r < A.resistanceLength := by dsimp only [r]; linarith [haR.2]
  have hcenterMem : A.resistance a ∈ Icc l r := by
    dsimp only [l, r]
    exact ⟨by linarith [haR.1], by linarith [haR.2]⟩
  filter_upwards [reversibleResistancePhysicalBand_continuous_average_ae A x T S hS l r hl hlr hr,
    reflectedLocalTimeSpatialVersion_fixed_level_all_times A.resistanceLength A.resistanceLength_pos
      1 zero_lt_one (A.resistance x) S
      (reflectedSpatialWindowPoint A.resistanceLength l r hl hlr hr (A.resistance a))]
    with ω hocc hcenter
  let V := fun y => reflectedLocalTimeWindowVersion A.resistanceLength A.resistanceLength_pos
    1 zero_lt_one (A.resistance x) S l r hl hlr hr y ω
  have hV : Continuous V := reflectedLocalTimeWindowVersion_continuous A.resistanceLength
    A.resistanceLength_pos 1 zero_lt_one (A.resistance x) S l r hl hlr hr ω
  have hc (s : BrownianCompactTime S) : V (A.resistance a) s =
      reflectedInteriorOccupationCoefficient (A.resistance x) (Real.sqrt (2 * 1))
        A.resistanceLength (A.resistance a) s.val ω := by
    have he := hcenter s
    rw [reflectedSpatialWindowPoint_of_mem A.resistanceLength l r hl hlr hr hcenterMem] at he
    exact he
  have hlim : Tendsto (fun h : ℝ =>
      ‖resistancePhysicalWeightedAverage A V a h - V (A.resistance a)‖) (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((resistancePhysicalWeightedAverage_tendsto A hV (Ioo_subset_Icc_self ha)).sub_const
        (V (A.resistance a))).norm
  apply squeeze_zero' (Eventually.of_forall (fun h => Real.iSup_nonneg (fun t => abs_nonneg _))) ?_ hlim
  obtain ⟨δ, hδ, hw⟩ := reversibleResistancePhysicalBand_window A ha
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with h hp hsmall
  have hb : Ioo (a - h) (a + h) ⊆ Ioo A.source.left A.source.right := by
    intro z hz
    exact (hw z ((abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩).trans hsmall)).1
  have hw' : ∀ z, |z - a| < h → A.resistance z ∈ Icc l r := by
    intro z hz
    exact Ioo_subset_Icc_self (hw z (hz.trans hsmall)).2
  apply ciSup_le
  intro t
  rw [hocc a h hp hb hw' t]
  let s := reversibleResistanceCompactInverseTime A x T S hS t ω
  change |resistancePhysicalWeightedAverage A V a h s -
    reflectedInteriorOccupationCoefficient (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a) s.val ω| ≤ _
  rw [← hc s]
  exact (resistancePhysicalWeightedAverage A V a h - V (A.resistance a)).norm_coe_le_norm s

end TimeTraps.Probability
