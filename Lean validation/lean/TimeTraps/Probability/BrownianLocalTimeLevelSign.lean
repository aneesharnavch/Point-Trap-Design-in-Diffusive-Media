module

public import TimeTraps.Probability.BrownianLocalTimeLevelProcess

@[expose] public section

/-! The level parameter acts continuously in the actual product-L²
closed integrand space and in the stochastic integral's L² target. These
are norm-topology statements, not continuity of a pointwise spatial
version of the process. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSignProcessL2_level_tendsto (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (𝓝 a)) (T : ℝ≥0) :
    Tendsto (fun n => brownianSignProcessL2 B (u n) T (brownianSignProcess_memLp hB hjoint (u n) T))
      atTop (𝓝 (brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T))) := by
  let A (n : ℕ) := brownianSignProcessL2 B (u n) T (brownianSignProcess_memLp hB hjoint (u n) T)
  let S := brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T)
  have he (n : ℕ) : ‖A n - S‖ ^ 2 = ∫ p,
      (brownianSignProcess B (u n) T p - brownianSignProcess B a T p) ^ 2
        ∂(volume : Measure ℝ).prod P := by
    calc
      _ = ∫ p, (A n - S) p ^ 2 ∂(volume : Measure ℝ).prod P := by
        simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp (A n - S))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (A n) S,
          brownianSignProcessL2_coe B (u n) T (brownianSignProcess_memLp hB hjoint (u n) T),
          brownianSignProcessL2_coe B a T (brownianSignProcess_memLp hB hjoint a T)] with p hd ha hs
        rw [hd, Pi.sub_apply, ha, hs]
  have hs : Tendsto (fun n => ‖A n - S‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using brownianSignProcess_level_squared_error_tendsto hB hjoint hu T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

theorem brownianSignProcessL2_level_continuous (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Continuous (fun a => brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T)) := by
  apply continuous_iff_seqContinuous.mpr
  intro u a hu
  exact brownianSignProcessL2_level_tendsto hB hjoint hu T

theorem brownianSignIntegrand_level_continuous (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Continuous (fun a => brownianSignIntegrand hB hBm hjoint a T) := by
  apply continuous_iff_seqContinuous.mpr
  intro u a hu
  exact tendsto_subtype_rng.mpr (brownianSignProcessL2_level_tendsto hB hjoint hu T)

theorem brownianSignIntegral_level_continuous (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Continuous (fun a => brownianSignIntegral hB hBm hjoint a T) :=
  (brownianIntegral hB).continuous.comp (brownianSignIntegrand_level_continuous hB hBm hjoint T)

theorem brownianDyadicSignIntegrand_level_continuous (T : ℝ≥0) :
    Continuous (fun a => brownianDyadicSignIntegrand a T) :=
  brownianSignIntegrand_level_continuous brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T

theorem brownianDyadicSignIntegral_level_continuous (T : ℝ≥0) :
    Continuous (fun a => brownianDyadicSignIntegral a T) :=
  brownianSignIntegral_level_continuous brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T

end TimeTraps.Probability
