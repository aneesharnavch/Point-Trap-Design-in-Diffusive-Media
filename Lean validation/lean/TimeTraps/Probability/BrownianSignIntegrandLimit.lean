module

public import TimeTraps.Probability.BrownianSignIntegrandLimitProcess

@[expose] public section

/-! Approximation-independent convergence to the actual sign integrand
and stochastic integral, including the constructed Brownian process. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℕ → ℝ → ℝ} {K : ℕ → ℝ≥0} {a : ℝ}

theorem brownianSignIntegrand_general_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : ∀ n, LipschitzWith (K n) (g n)) (hb : ∀ n x, |g n x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (Real.sign (x - a)))) (T : ℝ≥0) :
    Tendsto (fun n => brownianLipschitzIntegrand hB hBm (hg n) hjoint T)
      atTop (𝓝 (brownianSignIntegrand hB hBm hjoint a T)) :=
  tendsto_subtype_rng.mpr (brownianSignProcessL2_general_tendsto hB hjoint hg hb hlim T)

theorem brownianSignIntegral_general_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : ∀ n, LipschitzWith (K n) (g n)) (hb : ∀ n x, |g n x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (Real.sign (x - a)))) (T : ℝ≥0) :
    Tendsto (fun n => brownianIntegral hB (brownianLipschitzIntegrand hB hBm (hg n) hjoint T)) atTop
      (𝓝 (brownianSignIntegral hB hBm hjoint a T)) :=
  (brownianIntegral hB).continuous.continuousAt.tendsto.comp
    (brownianSignIntegrand_general_tendsto hB hBm hjoint hg hb hlim T)

theorem brownianDyadicSignIntegral_general_tendsto
    (hg : ∀ n, LipschitzWith (K n) (g n)) (hb : ∀ n x, |g n x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (Real.sign (x - a)))) (T : ℝ≥0) :
    Tendsto (fun n => brownianStochasticIntegral (brownianDyadicLipschitzIntegrand (hg n) T))
      atTop (𝓝 (brownianDyadicSignIntegral a T)) :=
  brownianSignIntegral_general_tendsto brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable hg hb hlim T

end TimeTraps.Probability
