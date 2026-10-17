module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-! The canonical unit-exponential threshold on a product probability space.
The first coordinate retains the full path, with no path-process or local-time
construction assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory

theorem unitExponential_probability : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure zero_lt_one

theorem unitExponential_tail (a : ℝ) (ha : 0 ≤ a) :
    expMeasure (1 : ℝ) (Ioi a) = ENNReal.ofReal (Real.exp (-a)) := by
  let _ := unitExponential_probability
  have hc : (expMeasure (1 : ℝ)).real (Iic a) = 1 - Real.exp (-a) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq zero_lt_one, if_pos ha, one_mul]
  have ht : (expMeasure (1 : ℝ)).real (Ioi a) = Real.exp (-a) := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, hc]
    ring
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    congrArg ENNReal.ofReal ht

theorem unitExponential_positive : expMeasure (1 : ℝ) (Ioi 0) = 1 := by
  simpa only [neg_zero, Real.exp_zero, ENNReal.ofReal_one] using unitExponential_tail 0 le_rfl

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def exponentialKillingMeasure : Measure (Ω × ℝ) := μ.prod (expMeasure 1)

theorem exponentialKilling_probability : IsProbabilityMeasure (exponentialKillingMeasure μ) := by
  let _ := unitExponential_probability
  exact inferInstanceAs (IsProbabilityMeasure (μ.prod (expMeasure 1)))

omit [IsProbabilityMeasure μ] in
theorem exponentialKilling_path_law :
    Measure.map Prod.fst (exponentialKillingMeasure μ) = μ := by
  let _ := unitExponential_probability
  simp only [exponentialKillingMeasure, Measure.map_fst_prod, measure_univ, one_smul]

theorem exponentialKilling_threshold_law :
    Measure.map Prod.snd (exponentialKillingMeasure μ) = expMeasure (1 : ℝ) := by
  let _ := unitExponential_probability
  simp only [exponentialKillingMeasure, Measure.map_snd_prod, measure_univ, one_smul]

theorem exponentialKilling_independent :
    IndepFun (Prod.fst : Ω × ℝ → Ω) Prod.snd (exponentialKillingMeasure μ) := by
  let _ := unitExponential_probability
  exact indepFun_prod (μ := μ) (ν := expMeasure 1) (X := id) (Y := id) measurable_id measurable_id

end TimeTraps.Probability
