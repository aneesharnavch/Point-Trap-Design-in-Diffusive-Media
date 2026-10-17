module

public import TimeTraps.Probability.ReflectedAtomicSurvivalExpectationTime
public import TimeTraps.Analysis.SurvivalIntegralTail

@[expose] public section

/-! Conditional tail consequences for the actual mean survival. The
uniform bound on expected finite-horizon survival time is an explicit
hypothesis, to be supplied by a separate analytic solution argument. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicMeanSurvival_le_div_of_expected_bound
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {C : ℝ}
    (hC : ∀ T : ℝ≥0, (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival L D x a κ r.toNNReal ω) ∂brownianDyadicMeasure) ≤ C)
    {T : ℝ≥0} (hT : 0 < T) :
    reflectedAtomicMeanSurvival L D x a κ T ≤ C / T.val := by
  apply survivalIntegralTail_le_div (C := C)
    (reflectedAtomicMeanSurvival_antitone L hL D hD x a κ hκ) _ hT
  intro S
  rw [← reflectedAtomicSurvival_mean_time_integral L hD x a κ hκ S]
  exact hC S

theorem reflectedAtomicMeanSurvival_tendsto_of_expected_bound
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {C : ℝ}
    (hC : ∀ T : ℝ≥0, (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival L D x a κ r.toNNReal ω) ∂brownianDyadicMeasure) ≤ C) :
    Tendsto (reflectedAtomicMeanSurvival L D x a κ) atTop (𝓝 0) := by
  apply survivalIntegralTail_tendsto (C := C)
    (reflectedAtomicMeanSurvival_antitone L hL D hD x a κ hκ)
    (fun T => (reflectedAtomicMeanSurvival_bounds L hD x a κ hκ T).1)
  intro T
  rw [← reflectedAtomicSurvival_mean_time_integral L hD x a κ hκ T]
  exact hC T

theorem reflectedAtomicMeanSurvival_residual_tendsto_of_expected_bound
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) {C : ℝ}
    (hC : ∀ T : ℝ≥0, (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival L D x a κ r.toNNReal ω) ∂brownianDyadicMeasure) ≤ C)
    {r : ℝ≥0 → ℝ} {M : ℝ}
    (hr : ∀ T, |r T| ≤ M * reflectedAtomicMeanSurvival L D x a κ T) :
    Tendsto r atTop (𝓝 0) := by
  apply survivalIntegralTail_residual_tendsto (C := C)
    (reflectedAtomicMeanSurvival_antitone L hL D hD x a κ hκ)
    (fun T => (reflectedAtomicMeanSurvival_bounds L hD x a κ hκ T).1) _ hr
  intro T
  rw [← reflectedAtomicSurvival_mean_time_integral L hD x a κ hκ T]
  exact hC T

end TimeTraps.Probability
