module

public import TimeTraps.Probability.BrownianItoC2Formula
public import TimeTraps.Probability.BrownianIntegralMean

@[expose] public section

/-! The actual C² Brownian function increment belongs to L2 and its
expectation is half the expectation of the genuine second-derivative
time integral. Only the global second-derivative bound is assumed; the
initial term is retained and no time/probability interchange is asserted. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℝ → ℝ}

theorem brownianItoC2_difference_memLp (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MemLp (fun ω => F (B T ω) - F (B 0 ω)) 2 P := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  exact (memLp_congr_ae (brownianItoC2_formula hB hBm hF h₂ hjoint T)).mpr
    ((Lp.memLp (brownianIntegral hB.toIsPreBrownianReal
      (brownianItoC2Integrand hB.toIsPreBrownianReal hBm hF h₂ hjoint T))).add
      ((brownianItoC2_drift_memLp hF h₂ hjoint T).const_mul (1 / 2 : ℝ)))

theorem brownianItoC2_difference_integrable (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Integrable (fun ω => F (B T ω) - F (B 0 ω)) P := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  exact (brownianItoC2_difference_memLp hB hBm hF h₂ hjoint T).integrable (by norm_num)

theorem brownianItoC2_difference_mean (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 2 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    (∫ ω, F (B T ω) - F (B 0 ω) ∂P) =
      (1 / 2 : ℝ) * ∫ ω, brownianItoDrift B (deriv (deriv F)) T ω ∂P := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hi := (Lp.memLp (brownianIntegral hB.toIsPreBrownianReal
    (brownianItoC2Integrand hB.toIsPreBrownianReal hBm hF h₂ hjoint T))).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hd := (brownianItoC2_drift_memLp (P := P) hF h₂ hjoint T).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ = ∫ ω, brownianIntegral hB.toIsPreBrownianReal
        (brownianItoC2Integrand hB.toIsPreBrownianReal hBm hF h₂ hjoint T) ω +
        (1 / 2 : ℝ) * brownianItoDrift B (deriv (deriv F)) T ω ∂P :=
      integral_congr_ae (brownianItoC2_formula hB hBm hF h₂ hjoint T)
    _ = _ := by
      rw [integral_add hi (hd.const_mul _), integral_const_mul, brownianIntegral_mean, zero_add]

end TimeTraps.Probability
