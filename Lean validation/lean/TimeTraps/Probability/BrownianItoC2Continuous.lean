module

public import TimeTraps.Probability.BrownianItoC2Formula
public import TimeTraps.Probability.BrownianItoDriftContinuity

@[expose] public section

/-! The actual continuous stochastic integral satisfies the C² Itô
identity simultaneously throughout a fixed compact horizon. A countable
dense set and continuity promote the fixed-time identities. The global
second-derivative bound remains explicit; no third derivative is used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal ENNReal

variable {F : ℝ → ℝ}

theorem brownianItoC2_formula_continuous_ae (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      F (brownianDyadicPath t ω) - F (brownianDyadicPath 0 ω) =
        brownianItoC2IntegralPath hF h₂ T t ω +
          (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) t ω := by
  have ht (t : BrownianCompactTime T) : ∀ᵐ ω ∂brownianDyadicMeasure,
      F (brownianDyadicPath t.val ω) - F (brownianDyadicPath 0 ω) =
        brownianItoC2IntegralPath hF h₂ T t.val ω +
          (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) t.val ω := by
    filter_upwards [brownianDyadicPath_itoC2_formula hF h₂ t.val,
      brownianItoC2IntegralPath_integral_ae hF h₂ t.property.2] with ω he hi
    rw [hi]
    exact he
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      F (brownianDyadicPath (denseSeq (BrownianCompactTime T) n).val ω) - F (brownianDyadicPath 0 ω) =
        brownianItoC2IntegralPath hF h₂ T (denseSeq (BrownianCompactTime T) n).val ω +
          (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F))
            (denseSeq (BrownianCompactTime T) n).val ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime T) n))
  filter_upwards [brownianDyadicPath_continuous_ae, hall] with ω hω hq
  have hl : Continuous (fun t : ℝ≥0 => F (brownianDyadicPath t ω) - F (brownianDyadicPath 0 ω)) :=
    (hF.continuous.comp hω).sub continuous_const
  have hr : Continuous (fun t : ℝ≥0 => brownianItoC2IntegralPath hF h₂ T t ω +
      (1 / 2 : ℝ) * brownianItoDrift brownianDyadicPath (deriv (deriv F)) t ω) :=
    (brownianItoC2IntegralPath_continuous hF h₂ T ω).add
      ((brownianItoDrift_continuous (brownianItoC2_secondDerivative_continuous hF) hω).const_mul (1 / 2 : ℝ))
  have he := (denseRange_denseSeq (BrownianCompactTime T)).equalizer
    (hl.comp continuous_subtype_val) (hr.comp continuous_subtype_val) (funext hq)
  intro t ht
  exact congrFun he ⟨t, zero_le, ht⟩

end TimeTraps.Probability
