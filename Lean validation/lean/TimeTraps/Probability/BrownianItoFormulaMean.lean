module

public import TimeTraps.Probability.BrownianItoFormula
public import TimeTraps.Probability.BrownianIntegralMean

@[expose] public section

/-! The actual Brownian increment of F is square-integrable and its
expectation is half the expectation of the ordinary second-derivative
drift. No separate integrability premise on F itself is imposed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℝ → ℝ}

theorem brownianIto_difference_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M₂ M₃ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MemLp (fun ω => F (B T ω) - F (B 0 ω)) 2 P :=
  (memLp_congr_ae (brownianIto_formula hB hBm hF h₂ h₃ hjoint T)).mpr
    ((Lp.memLp (brownianIntegral hB (brownianItoIntegrand hB hBm hF h₂ hjoint T))).add
      ((brownianIto_drift_memLp hB hF h₃ hjoint T).const_mul (1 / 2 : ℝ)))

theorem brownianIto_difference_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M₂ M₃ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Integrable (fun ω => F (B T ω) - F (B 0 ω)) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownianIto_difference_memLp hB hBm hF h₂ h₃ hjoint T).integrable (by norm_num)

theorem brownianIto_difference_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M₂ M₃ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    (∫ ω, F (B T ω) - F (B 0 ω) ∂P) =
      (1 / 2 : ℝ) * ∫ ω, brownianItoDrift B (deriv (deriv F)) T ω ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hi := (Lp.memLp (brownianIntegral hB
    (brownianItoIntegrand hB hBm hF h₂ hjoint T))).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hd := (brownianIto_drift_memLp hB hF h₃ hjoint T).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ = ∫ ω, brownianIntegral hB (brownianItoIntegrand hB hBm hF h₂ hjoint T) ω +
        (1 / 2 : ℝ) * brownianItoDrift B (deriv (deriv F)) T ω ∂P :=
      integral_congr_ae (brownianIto_formula hB hBm hF h₂ h₃ hjoint T)
    _ = _ := by
      rw [integral_add hi (hd.const_mul _), integral_const_mul, brownianIntegral_mean, zero_add]

end TimeTraps.Probability
