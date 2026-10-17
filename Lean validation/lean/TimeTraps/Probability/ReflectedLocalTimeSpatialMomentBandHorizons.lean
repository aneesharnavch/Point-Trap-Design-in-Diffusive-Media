module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentBandAlmostSure

@[expose] public section

/-! A single event works for every natural compact horizon. The original
literal occupation formula converges along the full positive-radius filter,
and hence along every deterministic positive sequence tending to zero. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedOccupationBand_literal_formula (L D x a h : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedOccupationBand L D x a h t ω =
      (1 / (2 * h)) * ∫ s in (0 : ℝ)..t.val,
        if |foldedTrajectory L D x brownianDyadicPath s.toNNReal ω - a| < h then (1 : ℝ) else 0 := by
  simp only [reflectedOccupationBand, brownianBandOccupation, brownianItoDrift, brownianBandIndicator_apply]

theorem reflectedOccupationBand_all_natural_horizons_as (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ N : ℕ,
      Tendsto (fun h : ℝ => ⨆ t : BrownianCompactTime (N : ℝ≥0),
        |reflectedOccupationBand L D x a.val h t.val ω -
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|)
        (𝓝[>] 0) (𝓝 0) :=
  ae_all_iff.mpr (fun N => reflectedOccupationBand_compact_uniform_as L hL D hD x (N : ℝ≥0) a)

theorem reflectedOccupationBand_all_horizon_sequences_as (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a : Ioo (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ N : ℕ, ∀ h : ℕ → ℝ,
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      Tendsto (fun n => ⨆ t : BrownianCompactTime (N : ℝ≥0),
        |reflectedOccupationBand L D x a.val (h n) t.val ω -
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω|)
        atTop (𝓝 0) := by
  filter_upwards [reflectedOccupationBand_all_natural_horizons_as L hL D hD x a] with ω hω
  intro N h hp hlim
  exact (hω N).comp (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hp⟩)

end TimeTraps.Probability
