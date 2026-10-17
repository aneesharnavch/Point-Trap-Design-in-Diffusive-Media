module

public import TimeTraps.Probability.ExponentialKilling

@[expose] public section

/-! Conditional survival in its path-event characterization. The identity
is derived by integrating the exponential tail over product-measure fibers. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

def exponentialSurvivalEvent (A : Ω → ℝ) : Set (Ω × ℝ) := {p | A p.1 < p.2}

theorem exponentialSurvivalEvent_measurable (A : Ω → ℝ) (hA : Measurable A) :
    MeasurableSet (exponentialSurvivalEvent A) :=
  measurableSet_lt (hA.comp measurable_fst) measurable_snd

theorem exponentialKilling_test_event_measurable (A : Ω → ℝ) (hA : Measurable A)
    (B : Set Ω) (hB : MeasurableSet B) :
    MeasurableSet {p : Ω × ℝ | p.1 ∈ B ∧ A p.1 < p.2} :=
  (hB.preimage measurable_fst).inter (exponentialSurvivalEvent_measurable A hA)

theorem exponentialSurvivalProbability_measurable (A : Ω → ℝ) (hA : Measurable A) :
    Measurable (fun ω => ENNReal.ofReal (Real.exp (-A ω))) := by fun_prop

theorem exponentialSurvivalProbability_le_one (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (Real.exp (-a)) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha))

variable (μ : Measure Ω)

theorem exponentialKilling_conditional_survival (A : Ω → ℝ) (hA : Measurable A)
    (hAnonneg : ∀ ω, 0 ≤ A ω) (B : Set Ω) (hB : MeasurableSet B) :
    exponentialKillingMeasure μ {p : Ω × ℝ | p.1 ∈ B ∧ A p.1 < p.2} =
      ∫⁻ ω in B, ENNReal.ofReal (Real.exp (-A ω)) ∂μ := by
  let _ := unitExponential_probability
  rw [exponentialKillingMeasure, Measure.prod_apply (exponentialKilling_test_event_measurable A hA B hB)]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro ω
  by_cases hω : ω ∈ B
  · rw [indicator_of_mem hω]
    have hs : Prod.mk ω ⁻¹' {p : Ω × ℝ | p.1 ∈ B ∧ A p.1 < p.2} = Ioi (A ω) := by
      ext e
      simp [hω]
    rw [hs, unitExponential_tail _ (hAnonneg ω)]
  · rw [indicator_of_notMem hω]
    have hs : Prod.mk ω ⁻¹' {p : Ω × ℝ | p.1 ∈ B ∧ A p.1 < p.2} = ∅ := by
      ext e
      simp [hω]
    rw [hs, measure_empty]

theorem exponentialKilling_survival (A : Ω → ℝ) (hA : Measurable A)
    (hAnonneg : ∀ ω, 0 ≤ A ω) :
    exponentialKillingMeasure μ (exponentialSurvivalEvent A) =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-A ω)) ∂μ := by
  simpa only [mem_univ, true_and, Measure.restrict_univ, exponentialSurvivalEvent] using
    exponentialKilling_conditional_survival μ A hA hAnonneg univ MeasurableSet.univ

end TimeTraps.Probability
