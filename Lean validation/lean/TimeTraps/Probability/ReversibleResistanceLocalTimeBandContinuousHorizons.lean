module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandContinuousLimit

@[expose] public section

/-! Source-formula and simultaneous-horizon wrappers for the physical
speed-mass normalized almost-sure occupation limit. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistancePhysicalBand_literal_compact_uniform_as
    (A : IntervalMedium) (x : ℝ) {a : ℝ}
    (ha : a ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime T,
        |(∫ s in (0 : ℝ)..t.val.val,
          if |reversibleResistancePath A x s.toNNReal ω - a| < h then (1 : ℝ) else 0) /
            (∫ z in Ioo (a - h) (a + h), A.source.density z) -
          reversibleResistanceLocalTime A x a t.val ω|) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [reversibleResistancePhysicalOccupationBand_compact_uniform_as A x ha T] with ω hω
  apply hω.congr'
  have hp : 0 < min (a - A.source.left) (A.source.right - a) :=
    lt_min (sub_pos.mpr ha.1) (sub_pos.mpr ha.2)
  filter_upwards [(eventually_lt_nhds hp).filter_mono nhdsWithin_le_nhds] with h hsmall
  have hb : Ioo (a - h) (a + h) ⊆ Icc A.source.left A.source.right := by
    intro z hz
    exact ⟨by linarith [(lt_min_iff.mp hsmall).1, hz.1],
      by linarith [(lt_min_iff.mp hsmall).2, hz.2]⟩
  congr 1
  funext t
  rw [reversibleResistancePhysicalOccupationBand_formula A x a h hb t.val ω]

theorem reversibleResistancePhysicalBand_all_natural_horizons_as
    (A : IntervalMedium) (x : ℝ) {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ N : ℕ,
      Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
        |reversibleResistancePhysicalOccupationBand A x a h t.val ω -
          reversibleResistanceLocalTime A x a t.val ω|) (𝓝[>] 0) (𝓝 0) :=
  ae_all_iff.mpr (fun N => reversibleResistancePhysicalOccupationBand_compact_uniform_as A x ha (N : ℝ≥0))

theorem reversibleResistancePhysicalBand_all_horizon_sequences_as
    (A : IntervalMedium) (x : ℝ) {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ N : ℕ, ∀ h : ℕ → ℝ,
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      Tendsto (fun n => ⨆ t : BrownianCompactTime (N : ℝ≥0),
        |reversibleResistancePhysicalOccupationBand A x a (h n) t.val ω -
          reversibleResistanceLocalTime A x a t.val ω|) atTop (𝓝 0) := by
  filter_upwards [reversibleResistancePhysicalBand_all_natural_horizons_as A x ha] with ω hω
  intro N h hp hlim
  exact (hω N).comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hp⟩)

end TimeTraps.Probability
