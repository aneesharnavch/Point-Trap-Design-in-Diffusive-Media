module

public import TimeTraps.Probability.KillingLifetimeMean

@[expose] public section

/-! The literal strict-exceedance lifetime for clocks whose continuous,
nondecreasing paths hold on one almost-sure event. That event is pulled
back to the independent-threshold product; no modification of the clock,
uncountable intersection of fixed-time events, or stopping-time claim is
used. The extended mean may still be infinite. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem contactLifetime_survival_iff_of_ae_paths
    (μ : Measure Ω) (A : ℝ → Ω → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hAt : Measurable (A t))
    (hp : ∀ᵐ ω ∂μ, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)) ∧
      MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    ∀ᵐ p : Ω × ℝ ∂exponentialKillingMeasure μ,
      (t : WithTop ℝ) < contactLifetime A p ↔ A t p.1 < p.2 := by
  have hprod : ∀ᵐ p : Ω × ℝ ∂exponentialKillingMeasure μ,
      ContinuousOn (fun s => A s p.1) (Ici (0 : ℝ)) ∧
        MonotoneOn (fun s => A s p.1) (Ici (0 : ℝ)) :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := expMeasure 1)).ae hp
  filter_upwards [hprod, exponentialKilling_threshold_ne μ (A t) hAt] with p hpath hne
  exact strictKillingTime_survival_iff (fun s => A s p.1) p.2 t ht hpath.1 hpath.2 hne

theorem contactLifetimeValue_aemeasurable_of_ae_paths
    (μ : Measure Ω) (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable (A t))
    (hp : ∀ᵐ ω ∂μ, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)) ∧
      MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    AEMeasurable (contactLifetimeValue A) (exponentialKillingMeasure μ) := by
  have hn : NullMeasurable (contactLifetimeValue A) (exponentialKillingMeasure μ) := by
    change @Measurable (NullMeasurableSpace (Ω × ℝ) (exponentialKillingMeasure μ)) ℝ≥0∞ _ _
      (contactLifetimeValue A)
    apply measurable_of_Ioi
    intro x
    change NullMeasurableSet (contactLifetimeValue A ⁻¹' Ioi x) (exponentialKillingMeasure μ)
    induction x using ENNReal.recTopCoe with
    | top => simpa only [Ioi_top, preimage_empty] using
        (nullMeasurableSet_empty : NullMeasurableSet (∅ : Set (Ω × ℝ)) (exponentialKillingMeasure μ))
    | coe r =>
      have hs : (contactLifetimeValue A ⁻¹' Ioi (r : ℝ≥0∞)) =
          {p : Ω × ℝ | ((r : ℝ) : WithTop ℝ) < contactLifetime A p} := by
        ext p
        change (r : ℝ≥0∞) < nonnegativeLifetimeValue (contactLifetime A p) ↔ _
        rw [← ENNReal.ofReal_coe_nnreal]
        exact nonnegativeLifetimeValue_lt_iff (r : ℝ) r.property _
      rw [hs]
      have he := (contactLifetime_survival_iff_of_ae_paths μ A r r.property
        (hA r r.property) hp).set_eq
      exact (exponentialSurvivalEvent_measurable (A r) (hA r r.property)).nullMeasurableSet.congr he.symm
  exact hn.aemeasurable

theorem contactLifetime_mean_survival_of_ae_paths
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable (A t))
    (hAnonneg : ∀ t : ℝ, 0 ≤ t → ∀ ω, 0 ≤ A t ω)
    (hp : ∀ᵐ ω ∂μ, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)) ∧
      MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    (∫⁻ p, contactLifetimeValue A p ∂exponentialKillingMeasure μ) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (Real.exp (-A t ω)) ∂μ := by
  let _ := exponentialKilling_probability μ
  rw [extendedLifetime_layercake (exponentialKillingMeasure μ) (contactLifetimeValue A)
    (contactLifetimeValue_aemeasurable_of_ae_paths μ A hA hp)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have he : {p : Ω × ℝ | ENNReal.ofReal t < contactLifetimeValue A p} =ᵐ[exponentialKillingMeasure μ]
      exponentialSurvivalEvent (A t) := by
    apply eventuallyEq_set.mpr
    filter_upwards [contactLifetime_survival_iff_of_ae_paths μ A t ht.le (hA t ht.le) hp] with p hsurv
    exact (nonnegativeLifetimeValue_lt_iff t ht.le (contactLifetime A p)).trans hsurv
  dsimp only
  rw [measure_congr he]
  exact exponentialKilling_survival μ (A t) (hA t ht.le) (hAnonneg t ht.le)

theorem contactLifetime_mean_identity_of_ae_paths
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ℝ → Ω → ℝ)
    (hA : Measurable (Function.uncurry A))
    (hAnonneg : ∀ t : ℝ, 0 ≤ t → ∀ ω, 0 ≤ A t ω)
    (hp : ∀ᵐ ω ∂μ, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)) ∧
      MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    (∫⁻ p, contactLifetimeValue A p ∂exponentialKillingMeasure μ) =
      ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-A t ω))) ∂μ := by
  have hAt : ∀ t : ℝ, 0 ≤ t → Measurable (A t) := by
    intro t _
    exact hA.comp (measurable_const.prodMk measurable_id)
  exact (contactLifetime_mean_survival_of_ae_paths μ A hAt hAnonneg hp).trans
    (contactLifetime_survival_tonelli μ A hA)

end TimeTraps.Probability
