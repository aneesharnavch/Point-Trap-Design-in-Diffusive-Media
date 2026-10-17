module

public import TimeTraps.Probability.KillingTime
public import TimeTraps.Probability.ExponentialKillingContact

@[expose] public section

/-! Survival of the actual strict-exceedance lifetime. A flat clock may
leave the lifetime beyond t when its value equals the threshold; the graph
of that single threshold has product measure zero. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

theorem unitExponential_singleton (a : ℝ) : expMeasure (1 : ℝ) {a} = 0 := by
  change (volume.withDensity (gammaPDF 1 1)) {a} = 0
  exact measure_singleton a

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exponentialKilling_threshold_graph_null (μ : Measure Ω) (A : Ω → ℝ)
    (hA : Measurable A) :
    exponentialKillingMeasure μ {p : Ω × ℝ | A p.1 = p.2} = 0 := by
  let _ := unitExponential_probability
  have hgraph : MeasurableSet {p : Ω × ℝ | A p.1 = p.2} :=
    measurableSet_eq_fun (hA.comp measurable_fst) measurable_snd
  rw [exponentialKillingMeasure, Measure.prod_apply hgraph]
  calc
    _ = ∫⁻ _ω : Ω, (0 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr
      intro ω
      have hs : Prod.mk ω ⁻¹' {p : Ω × ℝ | A p.1 = p.2} = {A ω} := by
        ext e
        simp [eq_comm]
      rw [hs, unitExponential_singleton]
    _ = 0 := lintegral_zero

theorem exponentialKilling_threshold_ne (μ : Measure Ω) (A : Ω → ℝ) (hA : Measurable A) :
    ∀ᵐ p : Ω × ℝ ∂exponentialKillingMeasure μ, A p.1 ≠ p.2 := by
  rw [ae_iff]
  simpa only [not_not] using exponentialKilling_threshold_graph_null μ A hA

noncomputable def contactLifetime (A : ℝ → Ω → ℝ) (p : Ω × ℝ) : WithTop ℝ :=
  strictKillingTime (fun t => A t p.1) p.2

theorem contactLifetime_survival_ae (μ : Measure Ω) (A : ℝ → Ω → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hAt : Measurable (A t))
    (hc : ∀ ω, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    ∀ᵐ p : Ω × ℝ ∂exponentialKillingMeasure μ,
      (t : WithTop ℝ) < contactLifetime A p ↔ A t p.1 < p.2 := by
  filter_upwards [exponentialKilling_threshold_ne μ (A t) hAt] with p hp
  exact strictKillingTime_survival_iff (fun s => A s p.1) p.2 t ht (hc p.1) (hm p.1) hp

theorem contactLifetime_survival_nullMeasurable (μ : Measure Ω) (A : ℝ → Ω → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hAt : Measurable (A t))
    (hc : ∀ ω, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    NullMeasurableSet {p : Ω × ℝ | (t : WithTop ℝ) < contactLifetime A p}
      (exponentialKillingMeasure μ) := by
  have he := (contactLifetime_survival_ae μ A t ht hAt hc hm).set_eq
  exact (exponentialSurvivalEvent_measurable (A t) hAt).nullMeasurableSet.congr he.symm

theorem contactLifetime_conditional_survival (μ : Measure Ω) (A : ℝ → Ω → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hAt : Measurable (A t)) (hAnonneg : ∀ ω, 0 ≤ A t ω)
    (hc : ∀ ω, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ)))
    (B : Set Ω) (hB : MeasurableSet B) :
    exponentialKillingMeasure μ
      {p : Ω × ℝ | p.1 ∈ B ∧ (t : WithTop ℝ) < contactLifetime A p} =
      ∫⁻ ω in B, ENNReal.ofReal (Real.exp (-A t ω)) ∂μ := by
  have he : {p : Ω × ℝ | p.1 ∈ B ∧ (t : WithTop ℝ) < contactLifetime A p} =ᵐ[exponentialKillingMeasure μ]
      {p : Ω × ℝ | p.1 ∈ B ∧ A t p.1 < p.2} := by
    apply eventuallyEq_set.mpr
    filter_upwards [contactLifetime_survival_ae μ A t ht hAt hc hm] with p hp
    exact and_congr Iff.rfl hp
  rw [measure_congr he]
  exact exponentialKilling_conditional_survival μ (A t) hAt hAnonneg B hB

theorem contactLifetime_survival (μ : Measure Ω) (A : ℝ → Ω → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hAt : Measurable (A t)) (hAnonneg : ∀ ω, 0 ≤ A t ω)
    (hc : ∀ ω, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    exponentialKillingMeasure μ {p : Ω × ℝ | (t : WithTop ℝ) < contactLifetime A p} =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-A t ω)) ∂μ := by
  simpa only [mem_univ, true_and, Measure.restrict_univ] using
    contactLifetime_conditional_survival μ A t ht hAt hAnonneg hc hm univ MeasurableSet.univ

end TimeTraps.Probability
