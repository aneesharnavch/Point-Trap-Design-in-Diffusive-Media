module

public import TimeTraps.Probability.BrownianTanakaCompensationMonotone
public import TimeTraps.Probability.BrownianIntegralMean

@[expose] public section

/-! The fixed-time Tanaka identity and expectation of the constructed
nonnegative compensation. The expectation uses the proved zero mean of
the actual sign stochastic integral. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaCompensation_formula (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    (fun ω => |B T ω - a| - |B 0 ω - a|) =ᵐ[P]
      (fun ω => brownianSignIntegral hB hBm hjoint a T ω +
        brownianTanakaCompensation hB hBm hjoint a T ω) := by
  filter_upwards [brownianTanakaCompensation_coe hB hBm hjoint a T] with ω hω
  linarith

theorem brownianTanakaCompensation_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Integrable (brownianTanakaCompensation hB hBm hjoint a T) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (Lp.memLp _).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem brownianTanakaCompensation_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianTanakaCompensation hB hBm hjoint a T ω ∂P) =
      ∫ ω, |B T ω - a| - |B 0 ω - a| ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hd := (brownianTanakaDifference_memLp hB a T).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  change Integrable (fun ω => |B T ω - a| - |B 0 ω - a|) P at hd
  have hi := (Lp.memLp (brownianSignIntegral hB hBm hjoint a T)).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  calc
    _ = ∫ ω, (|B T ω - a| - |B 0 ω - a|) - brownianSignIntegral hB hBm hjoint a T ω ∂P :=
      integral_congr_ae (brownianTanakaCompensation_coe hB hBm hjoint a T)
    _ = _ := by
      rw [integral_sub hd hi, brownianSignIntegral, brownianIntegral_mean, sub_zero]

end TimeTraps.Probability
