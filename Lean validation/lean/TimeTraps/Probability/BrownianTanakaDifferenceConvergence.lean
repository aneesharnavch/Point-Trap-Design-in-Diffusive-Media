module

public import TimeTraps.Probability.BrownianTanakaDifferenceApproximation

@[expose] public section

/-! Uniform measurable approximations of absolute value converge for
actual Brownian differences in L². Subtracting a convergent stochastic
term gives the corresponding compensation limit, without identifying
that limit as a local time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℕ → ℝ → ℝ} {a : ℝ} {ε : ℕ → ℝ}

theorem brownianTanakaApproxDifferenceL2_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ∀ n, Measurable (F n))
    (hε : ∀ n, 0 ≤ ε n) (hApprox : ∀ n x, |F n x - abs (x - a)| ≤ ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => brownianTanakaApproxDifferenceL2 B (F n) T
      (brownianTanakaApproxDifference_memLp hB hBm (hF n) (hApprox n) T)) atTop
      (𝓝 (brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have heps : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by simpa using hlim.const_mul 2
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => brownianTanakaApproxDifferenceL2_error_le hB (hε n) (hApprox n) T _ _) heps

theorem brownianTanakaCompensation_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (hF : ∀ n, Measurable (F n))
    (hε : ∀ n, 0 ≤ ε n) (hApprox : ∀ n x, |F n x - abs (x - a)| ≤ ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (T : ℝ≥0) (R : ℕ → Lp ℝ 2 P)
    (hR : Tendsto R atTop (𝓝 (brownianSignIntegral hB hBm hjoint a T))) :
    Tendsto (fun n => brownianTanakaApproxDifferenceL2 B (F n) T
      (brownianTanakaApproxDifference_memLp hB hBm (hF n) (hApprox n) T) - R n) atTop
      (𝓝 (brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T) -
        brownianSignIntegral hB hBm hjoint a T)) :=
  (brownianTanakaApproxDifferenceL2_tendsto hB hBm hF hε hApprox hlim T).sub hR

theorem brownianDyadicPath_absoluteDifference_tendsto (hF : ∀ n, Measurable (F n))
    (hε : ∀ n, 0 ≤ ε n) (hApprox : ∀ n x, |F n x - abs (x - a)| ≤ ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => brownianTanakaApproxDifferenceL2 brownianDyadicPath (F n) T
      (brownianTanakaApproxDifference_memLp brownianDyadicPath_isPreBrownianReal
        brownianDyadicPath_measurable (hF n) (hApprox n) T)) atTop
      (𝓝 (brownianTanakaDifferenceL2 brownianDyadicPath a T
        (brownianTanakaDifference_memLp brownianDyadicPath_isPreBrownianReal a T))) :=
  brownianTanakaApproxDifferenceL2_tendsto brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    hF hε hApprox hlim T

end TimeTraps.Probability
