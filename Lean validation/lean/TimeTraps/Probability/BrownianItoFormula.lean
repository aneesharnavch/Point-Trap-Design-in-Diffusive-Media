module

public import TimeTraps.Probability.BrownianItoFormulaStep
public import TimeTraps.Probability.BrownianItoFormulaLimit
public import TimeTraps.Probability.BrownianItoTaylorDyadic
public import TimeTraps.Probability.BrownianItoTaylorTelescope

@[expose] public section

/-! Brownian Itô's formula for C³ functions with globally bounded second
and third derivatives. The stochastic term is the actual completed
integral, the drift is the ordinary time integral, and equality is a.e.
No local/general Itô theorem or larger predictable-density premise is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℝ → ℝ}

theorem brownianIto_formula (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M₂ M₃ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    (fun ω => F (B T ω) - F (B 0 ω)) =ᵐ[P]
      (fun ω => brownianIntegral hB (brownianItoIntegrand hB hBm hF h₂ hjoint T) ω +
        (1 / 2 : ℝ) * brownianItoDrift B (deriv (deriv F)) T ω) := by
  let h₁ := brownianIto_firstDerivative_lipschitz hF h₂
  let h₂L := brownianIto_secondDerivative_lipschitz hF h₃
  let I (n : ℕ) : Lp ℝ 2 P := brownianIntegral hB (brownianLipschitzStepIntegrand hB hBm h₁ T n)
  let D (n : ℕ) : Lp ℝ 2 P := brownianItoDriftSumL2 B (deriv (deriv F)) T n
    (brownianItoDriftSum_memLp hB h₂L T n)
  let Q (n : ℕ) : Lp ℝ 2 P := brownianWeightedDyadicFunctionL2 B (deriv (deriv F)) T n
    (brownianWeightedDyadicFunction_memLp hB hBm h₂L.continuous.measurable M₂ h₂ T n)
  let Z : Lp ℝ 2 P := brownianIntegral hB (brownianItoIntegrand hB hBm hF h₂ hjoint T)
  let V : Lp ℝ 2 P := brownianItoDriftL2 B (deriv (deriv F)) T (brownianIto_drift_memLp hB hF h₃ hjoint T)
  let S (n : ℕ) : Lp ℝ 2 P := I n + (1 / 2 : ℝ) • D n + (1 / 2 : ℝ) • Q n
  let Y : Lp ℝ 2 P := Z + (1 / 2 : ℝ) • V
  let R (n : ℕ) : Lp ℝ 1 P := brownianItoTaylorSumL1 B F (brownianDyadicGrid T n)
    (brownianItoTaylorSum_integrable hB hBm hF h₃ _)
  have hI : Tendsto I atTop (𝓝 Z) := brownianIto_stochastic_step_tendsto hB hBm h₁ hjoint T
  have hD : Tendsto D atTop (𝓝 V) := brownianItoDriftL2_tendsto hB hBm h₂L hjoint T
  have hQ : Tendsto Q atTop (𝓝 0) :=
    brownianWeightedDyadicFunctionL2_tendsto hB hBm h₂L.continuous.measurable M₂ h₂ T
  have hS : Tendsto S atTop (𝓝 Y) := by
    have h := (hI.add (hD.const_smul (1 / 2 : ℝ))).add (hQ.const_smul (1 / 2 : ℝ))
    simpa only [smul_zero, add_zero] using h
  have hR : Tendsto R atTop (𝓝 0) := brownianItoTaylorDyadic_L1_tendsto hB hBm hF h₃ T
  have hSrep (n : ℕ) : S n =ᵐ[P] (fun ω =>
      (∑ i : Fin (2 ^ n), deriv F (B (brownianDyadicGrid T n i.castSucc) ω) *
        (B (brownianDyadicGrid T n i.succ) ω - B (brownianDyadicGrid T n i.castSucc) ω)) +
      (1 / 2 : ℝ) * brownianItoDriftSum B (deriv (deriv F)) T n ω +
      (1 / 2 : ℝ) * brownianWeightedDyadicFunction B (deriv (deriv F)) T n ω) := by
    filter_upwards [Lp.coeFn_add (I n + (1 / 2 : ℝ) • D n) ((1 / 2 : ℝ) • Q n),
      Lp.coeFn_add (I n) ((1 / 2 : ℝ) • D n), Lp.coeFn_smul (1 / 2 : ℝ) (D n),
      Lp.coeFn_smul (1 / 2 : ℝ) (Q n), brownianIto_stochastic_step_ae hB hBm h₁ T n,
      brownianItoDriftSumL2_coe B (deriv (deriv F)) T n (brownianItoDriftSum_memLp hB h₂L T n),
      brownianWeightedDyadicFunctionL2_coe B (deriv (deriv F)) T n
        (brownianWeightedDyadicFunction_memLp hB hBm h₂L.continuous.measurable M₂ h₂ T n)]
      with ω ha hb hd hq hi hdi hqi
    change (I n + (1 / 2 : ℝ) • D n + (1 / 2 : ℝ) • Q n) ω = _
    simp only [ha, Pi.add_apply, hb, hd, hq, Pi.smul_apply, smul_eq_mul]
    change I n ω + (1 / 2 : ℝ) * D n ω + (1 / 2 : ℝ) * Q n ω = _
    rw [hi, hdi, hqi]
  have hH (n : ℕ) : (fun ω => F (B T ω) - F (B 0 ω)) =ᵐ[P]
      (fun ω => S n ω + R n ω) := by
    filter_upwards [hSrep n, brownianItoTaylorSumL1_coe (brownianDyadicGrid T n)
      (brownianItoTaylorSum_integrable hB hBm hF h₃ _)] with ω hs hr
    rw [hs, hr]
    exact brownianItoTaylorDyadic_telescope B F T n ω
  have he := ae_eq_lp_limit_of_remainder S Y R (fun ω => F (B T ω) - F (B 0 ω)) hS hR hH
  refine he.trans ?_
  filter_upwards [Lp.coeFn_add Z ((1 / 2 : ℝ) • V), Lp.coeFn_smul (1 / 2 : ℝ) V,
    brownianItoDriftL2_coe B (deriv (deriv F)) T (brownianIto_drift_memLp hB hF h₃ hjoint T)]
    with ω ha hv hvi
  change (Z + (1 / 2 : ℝ) • V) ω = _
  simp only [ha, Pi.add_apply, hv, Pi.smul_apply, smul_eq_mul]
  change Z ω + (1 / 2 : ℝ) * V ω = _
  rw [hvi]

theorem brownianDyadicPath_ito_formula (hF : ContDiff ℝ 3 F)
    {M₂ M₃ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val) (T : ℝ≥0) :
    (fun ω => F (brownianDyadicPath T ω) - F (brownianDyadicPath 0 ω)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianStochasticIntegral
        (brownianItoIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
          hF h₂ brownianDyadicPath_jointly_measurable T) ω +
        (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) T ω) :=
  brownianIto_formula brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable hF h₂ h₃
    brownianDyadicPath_jointly_measurable T

end TimeTraps.Probability
