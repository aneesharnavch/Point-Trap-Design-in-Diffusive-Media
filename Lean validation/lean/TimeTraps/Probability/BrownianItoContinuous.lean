module

public import TimeTraps.Probability.BrownianItoFormulaMean
public import TimeTraps.Probability.BrownianItoDriftContinuity
public import TimeTraps.Probability.BrownianIntegralLipschitzCutoff
public import TimeTraps.Probability.BrownianIntegralContinuousGlobal

@[expose] public section

/-! The actual continuous stochastic integral satisfies smooth Itô's
formula simultaneously at every time of a fixed compact horizon. The
all-time assertion follows from the proved fixed-time formula, a countable
dense set and path continuity; it is not an uncountable AE intersection. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal ENNReal

variable {F : ℝ → ℝ}

noncomputable def brownianItoIntegralPath (hF : ContDiff ℝ 3 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) (T : ℝ≥0) :
    ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralGlobalPath
    (brownianDyadicLipschitzIntegrand (brownianIto_firstDerivative_lipschitz hF h₂) T)

theorem brownianItoIntegralPath_integral_ae (hF : ContDiff ℝ 3 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    {T t : ℝ≥0} (ht : t ≤ T) :
    brownianItoIntegralPath hF h₂ T t =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegral (brownianItoIntegrand brownianDyadicPath_isPreBrownianReal
        brownianDyadicPath_measurable hF h₂ brownianDyadicPath_jointly_measurable t) := by
  have he := brownianIntegralGlobalPath_integral_ae
    (brownianDyadicLipschitzIntegrand (brownianIto_firstDerivative_lipschitz hF h₂) T) t
  have hr := brownianLipschitzIntegral_upTo brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable (brownianIto_firstDerivative_lipschitz hF h₂)
    brownianDyadicPath_jointly_measurable T t
  rw [min_eq_left ht] at hr
  change brownianItoIntegralPath hF h₂ T t =ᵐ[brownianDyadicMeasure]
    brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t
      (brownianLipschitzIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        (brownianIto_firstDerivative_lipschitz hF h₂) brownianDyadicPath_jointly_measurable T) at he
  rw [hr] at he
  exact he

theorem brownianIto_formula_continuous_ae (hF : ContDiff ℝ 3 F)
    {M₂ M₃ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      F (brownianDyadicPath t ω) - F (brownianDyadicPath 0 ω) =
        brownianItoIntegralPath hF h₂ T t ω +
          (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) t ω := by
  have ht (t : BrownianCompactTime T) : ∀ᵐ ω ∂brownianDyadicMeasure,
      F (brownianDyadicPath t.val ω) - F (brownianDyadicPath 0 ω) =
        brownianItoIntegralPath hF h₂ T t.val ω +
          (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) t.val ω := by
    filter_upwards [brownianDyadicPath_ito_formula hF h₂ h₃ t.val,
      brownianItoIntegralPath_integral_ae hF h₂ t.property.2] with ω he hi
    rw [hi]
    exact he
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      F (brownianDyadicPath (denseSeq (BrownianCompactTime T) n).val ω) - F (brownianDyadicPath 0 ω) =
        brownianItoIntegralPath hF h₂ T (denseSeq (BrownianCompactTime T) n).val ω +
          (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F))
            (denseSeq (BrownianCompactTime T) n).val ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime T) n))
  filter_upwards [brownianDyadicPath_continuous_ae, hall] with ω hω hq
  have hl : Continuous (fun t : ℝ≥0 => F (brownianDyadicPath t ω) - F (brownianDyadicPath 0 ω)) :=
    (hF.continuous.comp hω).sub continuous_const
  have hd₁ : ContDiff ℝ 2 (deriv F) := hF.deriv'
  have hd₂ : ContDiff ℝ 1 (deriv (deriv F)) := hd₁.deriv'
  have hd : Continuous (deriv (deriv F)) := hd₂.continuous
  have hr : Continuous (fun t : ℝ≥0 => brownianItoIntegralPath hF h₂ T t ω +
      (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) t ω) :=
    (brownianIntegralGlobalPath_continuous _ ω).add
      ((brownianItoDrift_continuous hd hω).const_mul (1 / 2 : ℝ))
  have he := (denseRange_denseSeq (BrownianCompactTime T)).equalizer
    (hl.comp continuous_subtype_val) (hr.comp continuous_subtype_val) (funext hq)
  intro t ht
  exact congrFun he ⟨t, zero_le, ht⟩

end TimeTraps.Probability
