module

public import TimeTraps.Probability.BrownianPredictableSignPastFinite
public import TimeTraps.Probability.BrownianFoldUnitIntervalConvergence
public import TimeTraps.Probability.BrownianL2CharacteristicLimit

@[expose] public section

/-! The normalized fold-integral increment has its Gaussian mixed
characteristic identity against the original Brownian past. The finite
identity is proved on clipped grids and then transferred through actual
L² convergence. No law or independence premise is imposed on the limit. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldUnitInterval_mixed_char (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℂ} (hZi : Integrable Z P)
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z) (u : ℝ) (n : ℕ) :
    (∫ ω, Z ω * brownianRealChar u
      (brownianIntegral hB (brownianFoldUnitIntervalIntegrand hB hBm L hL x σ s t n) ω) ∂P) =
      (∫ ω, Z ω ∂P) * Complex.exp (-((t.val - s.val : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  have hvn : brownianPredictableSignVariance (brownianFoldUnitIntervalGrid s t n)
      (brownianFoldUnitIntervalGrid_monotone s t n) (fun _ => 1) = t - s := by
    rw [brownianPredictableSignVariance_one, brownianFoldUnitIntervalGrid_last hst,
      brownianFoldUnitIntervalGrid_zero]
  have hv := congrArg (fun a : ℝ≥0 => a.val) hvn
  change (∑ i : Fin (2 ^ n), (1 : ℝ) ^ 2 *
    ((brownianFoldUnitIntervalGrid s t n i.succ).val -
      (brownianFoldUnitIntervalGrid s t n i.castSucc).val)) = ((t - s : ℝ≥0) : ℝ) at hv
  rw [NNReal.coe_sub hst] at hv
  have hs : s ≤ brownianFoldUnitIntervalGrid s t n 0 := by rw [brownianFoldUnitIntervalGrid_zero]
  have hc := brownian_predictable_sign_earlier_char hB hBm hZi
    (brownianFoldUnitIntervalGrid s t n) (brownianFoldUnitIntervalGrid_monotone s t n)
    (brownianFoldUnitCoefficient B L x σ t n)
    (brownianFoldUnitIntervalCoefficient_adapted hBm L hL x σ s t n)
    (fun i => Eventually.of_forall (fun ω => brownianFoldUnitCoefficient_abs B L hL x σ t n i ω))
    (fun _ => 1) hs hZ u
  have hraw : (∫ ω, Z ω * brownianRealChar u
      (brownianStepIntegral B (brownianFoldUnitIntervalGrid s t n)
        (brownianFoldUnitCoefficient B L x σ t n) ω) ∂P) =
      (∫ ω, Z ω ∂P) * Complex.exp (-((t.val - s.val : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
    have hcoef : (fun (i : Fin (2 ^ n)) (ω : Ω) => (1 : ℝ) * brownianFoldUnitCoefficient B L x σ t n i ω) =
        brownianFoldUnitCoefficient B L x σ t n := by
      funext i ω
      exact one_mul _
    rw [hcoef, hv] at hc
    exact hc
  calc
    _ = ∫ ω, Z ω * brownianRealChar u
        (brownianStepIntegral B (brownianFoldUnitIntervalGrid s t n)
          (brownianFoldUnitCoefficient B L x σ t n) ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [brownianFoldUnitInterval_integral_ae hB hBm L hL x σ s t n] with ω hω
      rw [hω]
    _ = _ := hraw

theorem brownianFoldSlopeIntegral_increment_mixed_char (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℂ} (hZi : Integrable Z P)
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z) (u : ℝ) :
    (∫ ω, Z ω * brownianRealChar u
      ((brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ t -
        brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ s) ω) ∂P) =
      (∫ ω, Z ω ∂P) * Complex.exp (-((t.val - s.val : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  apply brownianL2_mixed_char_eq_of_tendsto
    (fun n => brownianIntegral hB.toIsPreBrownianReal
      (brownianFoldUnitIntervalIntegrand hB.toIsPreBrownianReal hBm L hL x σ s t n))
    _ Z hZi u _ (brownianFoldUnitIntervalIntegral_tendsto hB hBm hjoint L hL x hσ hst)
  exact fun n => brownianFoldUnitInterval_mixed_char hB.toIsPreBrownianReal hBm L hL x σ hst hZi hZ u n

end TimeTraps.Probability
