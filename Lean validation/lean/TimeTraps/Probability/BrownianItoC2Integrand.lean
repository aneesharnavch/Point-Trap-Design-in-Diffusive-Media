module

public import TimeTraps.Probability.BrownianIntegralLipschitzCutoff
public import TimeTraps.Probability.BrownianIntegralContinuousGlobal
public import TimeTraps.Probability.BrownianOccupationTimeBound
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Actual stochastic integrands and continuous integral paths for C²
functions with globally bounded second derivative. The genuine ordinary
drift is bounded and lies in L2. No third derivative assumption or Itô
formula is used in these constructions. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {F : ℝ → ℝ}

theorem brownianItoC2_firstDerivative_lipschitz (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) :
    LipschitzWith M₂ (deriv F) := by
  have hd : ContDiff ℝ 1 (deriv F) := hF.deriv'
  apply lipschitzWith_of_nnnorm_deriv_le (hd.differentiable (by norm_num))
  intro x
  change ‖deriv (deriv F) x‖ ≤ M₂.val
  simpa only [Real.norm_eq_abs] using h₂ x

theorem brownianItoC2_secondDerivative_continuous (hF : ContDiff ℝ 2 F) :
    Continuous (deriv (deriv F)) := by
  have hd : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have hdd : ContDiff ℝ 0 (deriv (deriv F)) := hd.deriv'
  exact hdd.continuous

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianItoC2Integrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianIntegralSpace B hBm P :=
  brownianLipschitzIntegrand hB hBm (brownianItoC2_firstDerivative_lipschitz hF h₂) hjoint T

theorem brownianItoC2Integrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    (brownianItoC2Integrand hB hBm hF h₂ hjoint T : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * deriv F (B p.1.toNNReal p.2)) :=
  brownianLipschitzIntegrand_coe hB hBm (brownianItoC2_firstDerivative_lipschitz hF h₂) hjoint T

theorem brownianItoC2Integrand_cutoff (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T t : ℝ≥0) :
    brownianTimeCutoff B hBm P t (brownianItoC2Integrand hB hBm hF h₂ hjoint T) =
      brownianItoC2Integrand hB hBm hF h₂ hjoint (min t T) :=
  brownianLipschitzIntegrand_cutoff hB hBm (brownianItoC2_firstDerivative_lipschitz hF h₂) hjoint T t

theorem brownianItoC2_drift_memLp [IsFiniteMeasure P] (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MemLp (brownianItoDrift B (deriv (deriv F)) T) 2 P :=
  brownianItoDrift_bounded_memLp (brownianItoC2_secondDerivative_continuous hF).measurable hjoint h₂ T

theorem brownianItoC2_drift_intervalIntegrable (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (ω : Ω) :
    IntervalIntegrable (fun s => deriv (deriv F) (B s.toNNReal ω)) volume 0 T.val :=
  brownianItoDrift_bounded_intervalIntegrable
    (brownianItoC2_secondDerivative_continuous hF).measurable hjoint h₂ T ω

noncomputable def brownianItoC2IntegralPath (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) (T : ℝ≥0) :
    ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralGlobalPath
    (brownianDyadicLipschitzIntegrand (brownianItoC2_firstDerivative_lipschitz hF h₂) T)

theorem brownianItoC2IntegralPath_integral_ae (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) {T t : ℝ≥0} (ht : t ≤ T) :
    brownianItoC2IntegralPath hF h₂ T t =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegral (brownianItoC2Integrand brownianDyadicPath_isPreBrownianReal
        brownianDyadicPath_measurable hF h₂ brownianDyadicPath_jointly_measurable t) := by
  have he := brownianIntegralGlobalPath_integral_ae
    (brownianDyadicLipschitzIntegrand (brownianItoC2_firstDerivative_lipschitz hF h₂) T) t
  have hr := brownianLipschitzIntegral_upTo brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable (brownianItoC2_firstDerivative_lipschitz hF h₂)
    brownianDyadicPath_jointly_measurable T t
  rw [min_eq_left ht] at hr
  change brownianItoC2IntegralPath hF h₂ T t =ᵐ[brownianDyadicMeasure]
    brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t
      (brownianLipschitzIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        (brownianItoC2_firstDerivative_lipschitz hF h₂) brownianDyadicPath_jointly_measurable T) at he
  rw [hr] at he
  exact he

theorem brownianItoC2IntegralPath_continuous (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianItoC2IntegralPath hF h₂ T t ω) :=
  brownianIntegralGlobalPath_continuous _ ω

theorem brownianItoC2IntegralPath_jointly_measurable (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianItoC2IntegralPath hF h₂ T p.1 p.2) :=
  brownianIntegralGlobalPath_jointlyMeasurable _

end TimeTraps.Probability
