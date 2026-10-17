module

public import TimeTraps.Probability.ReversibleResistanceSurvivalExpectation

@[expose] public section

/-! Exact conditional survival and layer-cake identities for the literal
first-attainment killing time of the physical variable-medium diffusion.
The tested identity holds for every measurable event of the entire driving
path; all clock hypotheses are derived for the constructed local times. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reversibleResistanceAttainmentLifetime_survival_iff_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      (t : WithTop ℝ) < reversibleResistanceAttainmentLifetime A x a κ p ↔
        reversibleResistanceAtomicClock A x a κ t p.1 < p.2 := by
  filter_upwards [reversibleResistanceLifetime_eq_attainment_ae A x a κ hκ,
    contactLifetime_survival_iff_of_ae_paths brownianDyadicMeasure
      (reversibleResistanceAtomicClock A x a κ) t ht
      (reversibleResistanceAtomicClock_measurable A x a κ t)
      (reversibleResistanceAtomicClock_paths_ae A x a κ hκ)] with p he hs
  rwa [← he]

theorem reversibleResistanceAttainmentLifetime_survival_nullMeasurable (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    NullMeasurableSet {p | (t : WithTop ℝ) < reversibleResistanceAttainmentLifetime A x a κ p}
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  have he := (reversibleResistanceAttainmentLifetime_survival_iff_ae A x a κ hκ t ht).set_eq
  exact (exponentialSurvivalEvent_measurable (reversibleResistanceAtomicClock A x a κ t)
    (reversibleResistanceAtomicClock_measurable A x a κ t)).nullMeasurableSet.congr he.symm

theorem reversibleResistanceAttainmentLifetime_conditional_survival (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    exponentialKillingMeasure brownianDyadicMeasure
      {p | p.1 ∈ B ∧ (t : WithTop ℝ) < reversibleResistanceAttainmentLifetime A x a κ p} =
      ∫⁻ ω in B, ENNReal.ofReal (reversibleResistanceAtomicSurvival A x a κ t.toNNReal ω)
        ∂brownianDyadicMeasure := by
  have he : {p | p.1 ∈ B ∧ (t : WithTop ℝ) < reversibleResistanceAttainmentLifetime A x a κ p}
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        {p | p.1 ∈ B ∧ reversibleResistanceAtomicClock A x a κ t p.1 < p.2} := by
    apply eventuallyEq_set.mpr
    filter_upwards [reversibleResistanceAttainmentLifetime_survival_iff_ae A x a κ hκ t ht] with p hp
    exact and_congr_right (fun _ => hp)
  exact (measure_congr he).trans
    (exponentialKilling_conditional_survival brownianDyadicMeasure
      (reversibleResistanceAtomicClock A x a κ t)
      (reversibleResistanceAtomicClock_measurable A x a κ t)
      (fun ω => reversibleResistanceAtomicHazard_nonneg A x a κ hκ t.toNNReal ω) B hB)

theorem reversibleResistanceAttainmentLifetime_survival_probability (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    exponentialKillingMeasure brownianDyadicMeasure
      {p | (t : WithTop ℝ) < reversibleResistanceAttainmentLifetime A x a κ p} =
      ENNReal.ofReal (reversibleResistanceMeanSurvival A x a κ t.toNNReal) := by
  have h := reversibleResistanceAttainmentLifetime_conditional_survival A x a κ hκ t ht
    univ MeasurableSet.univ
  simp only [mem_univ, true_and, Measure.restrict_univ] at h
  exact h.trans (reversibleResistanceAtomicSurvival_lintegral A x a κ hκ t.toNNReal)

theorem reversibleResistanceAttainmentLifetimeValue_mean_survival (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, reversibleResistanceAttainmentLifetimeValue A x a κ p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (reversibleResistanceMeanSurvival A x a κ r.toNNReal) := by
  refine (lintegral_congr_ae (reversibleResistanceLifetimeValue_eq_attainment_ae A x a κ hκ).symm).trans ?_
  refine (contactLifetime_mean_survival_of_ae_paths brownianDyadicMeasure
    (reversibleResistanceAtomicClock A x a κ)
    (fun t _ => reversibleResistanceAtomicClock_measurable A x a κ t)
    (fun t _ ω => reversibleResistanceAtomicHazard_nonneg A x a κ hκ t.toNNReal ω)
    (reversibleResistanceAtomicClock_paths_ae A x a κ hκ)).trans ?_
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact reversibleResistanceAtomicSurvival_lintegral A x a κ hκ t.toNNReal

theorem reversibleResistanceAttainmentLifetimeValue_mean_identity (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, reversibleResistanceAttainmentLifetimeValue A x a κ p
      ∂exponentialKillingMeasure brownianDyadicMeasure) =
      ∫⁻ ω, (∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (reversibleResistanceAtomicSurvival A x a κ r.toNNReal ω)) ∂brownianDyadicMeasure :=
  (lintegral_congr_ae (reversibleResistanceLifetimeValue_eq_attainment_ae A x a κ hκ).symm).trans
    (contactLifetime_mean_identity_of_ae_paths brownianDyadicMeasure
      (reversibleResistanceAtomicClock A x a κ)
      (reversibleResistanceAtomicClock_jointlyMeasurable A x a κ)
      (fun t _ ω => reversibleResistanceAtomicHazard_nonneg A x a κ hκ t.toNNReal ω)
      (reversibleResistanceAtomicClock_paths_ae A x a κ hκ))

end TimeTraps.Probability
