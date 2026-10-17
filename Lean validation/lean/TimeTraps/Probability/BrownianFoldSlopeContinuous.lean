module

public import TimeTraps.Probability.BrownianFoldSlopeCutoff
public import TimeTraps.Probability.BrownianIntegralContinuousGlobalCompact

@[expose] public section

/-! Continuous finite-horizon versions of the actual normalized fold
integral for the constructed Brownian process. The source integral is
identified by its proved cutoff relation, rather than a new process-space
density assumption. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def brownianDyadicFoldSlopeIntegrand (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) : BrownianIntegrand :=
  brownianFoldSlopeIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL x hσ T

def brownianDyadicFoldSlopeIntegral (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) : Lp ℝ 2 brownianDyadicMeasure :=
  brownianFoldSlopeIntegral brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL x hσ T

def brownianFoldSlopeHorizonPath (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) : ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralGlobalPath (brownianDyadicFoldSlopeIntegrand L hL x hσ T)

theorem brownianFoldSlopeHorizonPath_continuous (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianFoldSlopeHorizonPath L hL x hσ T t ω) :=
  brownianIntegralGlobalPath_continuous (brownianDyadicFoldSlopeIntegrand L hL x hσ T) ω

theorem brownianFoldSlopeHorizonPath_measurable (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T t : ℝ≥0) : Measurable (brownianFoldSlopeHorizonPath L hL x hσ T t) :=
  brownianIntegralGlobalPath_measurable (brownianDyadicFoldSlopeIntegrand L hL x hσ T) t

theorem brownianFoldSlopeHorizonPath_jointlyMeasurable (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianFoldSlopeHorizonPath L hL x hσ T p.1 p.2) :=
  brownianIntegralGlobalPath_jointlyMeasurable (brownianDyadicFoldSlopeIntegrand L hL x hσ T)

theorem brownianFoldSlopeHorizonPath_integral_ae (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T t : ℝ≥0) :
    brownianFoldSlopeHorizonPath L hL x hσ T t =ᵐ[brownianDyadicMeasure]
      brownianDyadicFoldSlopeIntegral L hL x hσ (min t T) := by
  have he := brownianIntegralGlobalPath_integral_ae (brownianDyadicFoldSlopeIntegrand L hL x hσ T) t
  change brownianFoldSlopeHorizonPath L hL x hσ T t =ᵐ[brownianDyadicMeasure]
    brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t
      (brownianFoldSlopeIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL x hσ T) at he
  rw [brownianFoldSlopeIntegral_upTo] at he
  exact he

theorem brownianFoldSlopeHorizonPath_zero_ae (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (T : ℝ≥0) :
    brownianFoldSlopeHorizonPath L hL x hσ T 0 =ᵐ[brownianDyadicMeasure] (fun _ => 0) := by
  have he := brownianFoldSlopeHorizonPath_integral_ae L hL x hσ T 0
  simp only [min_eq_left (show (0 : ℝ≥0) ≤ T from zero_le), brownianDyadicFoldSlopeIntegral,
    brownianFoldSlopeIntegral_zero] at he
  exact he.trans (Lp.coeFn_zero ℝ 2 brownianDyadicMeasure)

theorem brownianFoldSlopeHorizonPath_raw_aestronglyMeasurable (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (brownianFoldSlopeHorizonPath L hL x hσ T t)
      brownianDyadicMeasure :=
  brownianIntegralGlobalPath_raw_aestronglyMeasurable (brownianDyadicFoldSlopeIntegrand L hL x hσ T) t

end TimeTraps.Probability

end
