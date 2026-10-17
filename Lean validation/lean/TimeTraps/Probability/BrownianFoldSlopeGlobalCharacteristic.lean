module

public import TimeTraps.Probability.BrownianFoldSlopeMixedCharacteristic
public import TimeTraps.Probability.BrownianFoldSlopeGlobal

@[expose] public section

/-! The continuous normalized fold-noise version retains the exact
increment characteristic factorization against every integrable complex
multiplier measurable in the original Brownian past. All representative
identifications are explicitly almost everywhere at the fixed times. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianDyadicFoldSlope_increment_mixed_char (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) {s t : ℝ≥0} (hst : s ≤ t) {Z : (ℕ → ℝ) → ℂ}
    (hZi : Integrable Z brownianDyadicMeasure) (hZ : StronglyMeasurable[brownianFiltration s] Z) (u : ℝ) :
    (∫ ω, Z ω * brownianRealChar u
      ((brownianDyadicFoldSlopeIntegral L hL x hσ t - brownianDyadicFoldSlopeIntegral L hL x hσ s) ω)
        ∂brownianDyadicMeasure) =
      (∫ ω, Z ω ∂brownianDyadicMeasure) *
        Complex.exp (-((t.val - s.val : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) :=
  brownianFoldSlopeIntegral_increment_mixed_char brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ hst hZi hZ u

theorem brownianFoldSlopeGlobalPath_increment_mixed_char (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) {s t : ℝ≥0} (hst : s ≤ t) {Z : (ℕ → ℝ) → ℂ}
    (hZi : Integrable Z brownianDyadicMeasure) (hZ : StronglyMeasurable[brownianFiltration s] Z) (u : ℝ) :
    (∫ ω, Z ω * brownianRealChar u
      (brownianFoldSlopeGlobalPath L hL x hσ t ω - brownianFoldSlopeGlobalPath L hL x hσ s ω)
        ∂brownianDyadicMeasure) =
      (∫ ω, Z ω ∂brownianDyadicMeasure) *
        Complex.exp (-((t.val - s.val : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  calc
    _ = ∫ ω, Z ω * brownianRealChar u
        ((brownianDyadicFoldSlopeIntegral L hL x hσ t - brownianDyadicFoldSlopeIntegral L hL x hσ s) ω)
          ∂brownianDyadicMeasure := by
      apply integral_congr_ae
      filter_upwards [brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t,
        brownianFoldSlopeGlobalPath_integral_ae L hL x hσ s,
        Lp.coeFn_sub (brownianDyadicFoldSlopeIntegral L hL x hσ t)
          (brownianDyadicFoldSlopeIntegral L hL x hσ s)] with ω ht hs hd
      rw [ht, hs, hd, Pi.sub_apply]
    _ = _ := brownianDyadicFoldSlope_increment_mixed_char L hL x hσ hst hZi hZ u

end TimeTraps.Probability
