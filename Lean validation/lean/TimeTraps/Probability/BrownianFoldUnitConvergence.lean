module

public import TimeTraps.Probability.BrownianFoldUnitApproximation
public import TimeTraps.Probability.BrownianFoldSlopeContinuous

@[expose] public section

/-! The actual predictable unit-step integrands and their completed
stochastic integrals converge in L² to the canonical fold-slope objects.
At every positive grid time, the unit coefficient agrees almost surely
with the original slope; the initial coefficient remains truly unit. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldUnitCoefficient_eq_slope_ae (hB : IsPreBrownianReal B P)
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (n : ℕ)
    (i : Fin (2 ^ n)) (hi : 0 < brownianDyadicGrid T n i.castSucc) :
    brownianFoldUnitCoefficient B L x σ T n i =ᵐ[P]
      (fun ω => reflectedFoldSlope L (x + σ * B (brownianDyadicGrid T n i.castSucc) ω)) := by
  filter_upwards [brownian_affine_ne_lattice_eval_ae hB L x hσ hi] with ω hω
  exact reflectedFoldUnitSlope_eq L hL _ hω

theorem brownianFoldUnitStepIntegrand_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun n => brownianFoldUnitStepIntegrand hB.toIsPreBrownianReal hBm L hL x σ T n) atTop
      (𝓝 (brownianFoldSlopeIntegrand hB.toIsPreBrownianReal hBm hjoint L hL x hσ T)) := by
  let A (n : ℕ) : Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
    brownianFoldUnitStepIntegrand hB.toIsPreBrownianReal hBm L hL x σ T n
  let S : Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
    brownianFoldSlopeIntegrand hB.toIsPreBrownianReal hBm hjoint L hL x hσ T
  have he (n : ℕ) : ‖A n - S‖ ^ 2 = ∫ p, (brownianFoldUnitTimeGrid B L x σ T n p -
      brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2 ∂volume.prod P := by
    calc
      _ = ∫ p, (A n - S) p ^ 2 ∂volume.prod P := by
        simpa only [Lp.toLp_coeFn] using memLp_norm_toLp_sq (Lp.memLp (A n - S))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (A n) S,
          brownianFoldUnitStepIntegrand_coe hB.toIsPreBrownianReal hBm L hL x σ T n,
          brownianFoldSlopeIntegrand_coe hB.toIsPreBrownianReal hBm hjoint L hL x hσ T] with p hd ha hs
        rw [hd, Pi.sub_apply, ha, hs]
  have hs : Tendsto (fun n => ‖A n - S‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using brownianFoldUnitTimeGrid_squared_error_tendsto hB hBm hjoint L hL x hσ T
  apply tendsto_subtype_rng.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

theorem brownianFoldUnitStepIntegral_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun n => brownianIntegral hB.toIsPreBrownianReal
      (brownianFoldUnitStepIntegrand hB.toIsPreBrownianReal hBm L hL x σ T n)) atTop
      (𝓝 (brownianFoldSlopeIntegral hB.toIsPreBrownianReal hBm hjoint L hL x hσ T)) :=
  (brownianIntegral hB.toIsPreBrownianReal).continuous.continuousAt.tendsto.comp
    (brownianFoldUnitStepIntegrand_tendsto hB hBm hjoint L hL x hσ T)

theorem brownianDyadicFoldUnitStepIntegral_tendsto (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun n => brownianStochasticIntegral
      (brownianFoldUnitStepIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        L hL x σ T n)) atTop (𝓝 (brownianDyadicFoldSlopeIntegral L hL x hσ T)) :=
  brownianFoldUnitStepIntegral_tendsto brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL x hσ T

end TimeTraps.Probability
