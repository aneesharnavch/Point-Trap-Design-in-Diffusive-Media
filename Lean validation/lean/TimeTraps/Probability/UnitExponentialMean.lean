module

public import TimeTraps.Probability.ExponentialKilling
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! The actual independent unit-exponential threshold has finite mean
exactly one, derived from its proved survival function by layer cake. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter

theorem unitExponential_nonneg_ae : 0 ≤ᵐ[expMeasure (1 : ℝ)] (fun x : ℝ => x) := by
  let _ := unitExponential_probability
  have h : ∀ᵐ x ∂expMeasure (1 : ℝ), x ∈ Ioi 0 :=
    (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr unitExponential_positive
  exact h.mono fun _ hx => hx.le

theorem unitExponential_lintegral_mean :
    (∫⁻ x, ENNReal.ofReal x ∂expMeasure (1 : ℝ)) = 1 := by
  rw [lintegral_eq_lintegral_meas_lt _ unitExponential_nonneg_ae measurable_id.aemeasurable]
  have ht : (∫⁻ t in Ioi (0 : ℝ), expMeasure (1 : ℝ) {x : ℝ | t < x}) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact unitExponential_tail t ht.le
  rw [ht, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
    (Eventually.of_forall fun x => (Real.exp_pos (-x)).le), integral_exp_neg_Ioi_zero,
    ENNReal.ofReal_one]

theorem unitExponential_integrable : Integrable (fun x : ℝ => x) (expMeasure (1 : ℝ)) := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal unitExponential_nonneg_ae, unitExponential_lintegral_mean]
  exact ENNReal.one_lt_top

theorem unitExponential_mean : (∫ x, x ∂expMeasure (1 : ℝ)) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae unitExponential_nonneg_ae measurable_id.aestronglyMeasurable,
    unitExponential_lintegral_mean, ENNReal.toReal_one]

end TimeTraps.Probability
