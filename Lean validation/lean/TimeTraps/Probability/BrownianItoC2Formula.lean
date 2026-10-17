module

public import TimeTraps.Probability.BrownianItoC2Remainder
public import TimeTraps.Probability.BrownianItoC2Integrand
public import TimeTraps.Probability.BrownianItoPathwiseLimit
public import TimeTraps.Probability.BrownianItoDriftContinuousAdapted
public import TimeTraps.Probability.BrownianItoFormulaStep
public import TimeTraps.Probability.BrownianItoTaylorTelescope

@[expose] public section

/-! Actual Brownian Itô formula for a C2 function with globally bounded
second derivative. The proof combines exact dyadic telescoping, the
constructed L2 stochastic integral, bounded weighted quadratic errors,
ordinary drift convergence and compact pathwise Taylor remainders.
No third derivative or assumed stochastic change-of-variable formula is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℝ → ℝ}

theorem brownianItoC2_formula (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    (fun ω => F (B T ω) - F (B 0 ω)) =ᵐ[P]
      (fun ω => brownianIntegral hB.toIsPreBrownianReal
        (brownianItoC2Integrand hB.toIsPreBrownianReal hBm hF h₂ hjoint T) ω +
        (1 / 2 : ℝ) * brownianItoDrift B (deriv (deriv F)) T ω) := by
  let h₁ := brownianItoC2_firstDerivative_lipschitz hF h₂
  have hc := brownianItoC2_secondDerivative_continuous hF
  let I (n : ℕ) : Lp ℝ 2 P :=
    brownianIntegral hB.toIsPreBrownianReal (brownianLipschitzStepIntegrand hB.toIsPreBrownianReal hBm h₁ T n)
  let Q (n : ℕ) : Lp ℝ 2 P := brownianWeightedDyadicFunctionL2 B (deriv (deriv F)) T n
    (brownianWeightedDyadicFunction_memLp hB.toIsPreBrownianReal hBm hc.measurable M₂ h₂ T n)
  let Z : Lp ℝ 2 P := brownianIntegral hB.toIsPreBrownianReal
    (brownianItoC2Integrand hB.toIsPreBrownianReal hBm hF h₂ hjoint T)
  let S (n : ℕ) : Lp ℝ 2 P := I n + (1 / 2 : ℝ) • Q n
  let R (n : ℕ) (ω : Ω) : ℝ := (1 / 2 : ℝ) * brownianItoDriftSum B (deriv (deriv F)) T n ω +
    brownianItoTaylorSum B F (brownianDyadicGrid T n) ω
  let r (ω : Ω) : ℝ := (1 / 2 : ℝ) * brownianItoDrift B (deriv (deriv F)) T ω
  have hI : Tendsto I atTop (𝓝 Z) :=
    brownianIto_stochastic_step_tendsto hB.toIsPreBrownianReal hBm h₁ hjoint T
  have hQ : Tendsto Q atTop (𝓝 0) :=
    brownianWeightedDyadicFunctionL2_tendsto hB.toIsPreBrownianReal hBm hc.measurable M₂ h₂ T
  have hS : Tendsto S atTop (𝓝 Z) := by
    simpa only [smul_zero, add_zero] using hI.add (hQ.const_smul (1 / 2 : ℝ))
  have hR : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 (r ω)) := by
    filter_upwards [hB.cont, brownianItoTaylorDyadic_c2_ae_tendsto hB hF T] with ω hpath hrem
    have hd := brownianItoDriftSum_bounded_continuous_tendsto hc h₂ T ω hpath
    simpa only [add_zero] using (hd.const_mul (1 / 2 : ℝ)).add hrem
  have hSrep (n : ℕ) : S n =ᵐ[P] (fun ω =>
      (∑ i : Fin (2 ^ n), deriv F (B (brownianDyadicGrid T n i.castSucc) ω) *
        (B (brownianDyadicGrid T n i.succ) ω - B (brownianDyadicGrid T n i.castSucc) ω)) +
      (1 / 2 : ℝ) * brownianWeightedDyadicFunction B (deriv (deriv F)) T n ω) := by
    filter_upwards [Lp.coeFn_add (I n) ((1 / 2 : ℝ) • Q n), Lp.coeFn_smul (1 / 2 : ℝ) (Q n),
      brownianIto_stochastic_step_ae hB.toIsPreBrownianReal hBm h₁ T n,
      brownianWeightedDyadicFunctionL2_coe B (deriv (deriv F)) T n
        (brownianWeightedDyadicFunction_memLp hB.toIsPreBrownianReal hBm hc.measurable M₂ h₂ T n)]
      with ω ha hq hi hqi
    change (I n + (1 / 2 : ℝ) • Q n) ω = _
    simp only [ha, Pi.add_apply, hq, Pi.smul_apply, smul_eq_mul]
    change I n ω + (1 / 2 : ℝ) * Q n ω = _
    rw [hi, hqi]
  have hH (n : ℕ) : (fun ω => F (B T ω) - F (B 0 ω)) =ᵐ[P]
      (fun ω => S n ω + R n ω) := by
    filter_upwards [hSrep n] with ω hs
    rw [hs]
    dsimp only [R]
    have he := brownianItoTaylorDyadic_telescope B F T n ω
    linarith
  exact ae_eq_lp_limit_of_pathwise_remainder S Z R r (fun ω => F (B T ω) - F (B 0 ω)) hS hR hH

theorem brownianDyadicPath_itoC2_formula (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) (T : ℝ≥0) :
    (fun ω => F (brownianDyadicPath T ω) - F (brownianDyadicPath 0 ω)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianStochasticIntegral
        (brownianItoC2Integrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
          hF h₂ brownianDyadicPath_jointly_measurable T) ω +
        (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) T ω) :=
  brownianItoC2_formula brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable hF h₂
    brownianDyadicPath_jointly_measurable T

end TimeTraps.Probability
