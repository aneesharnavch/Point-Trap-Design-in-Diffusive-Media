module

public import TimeTraps.Probability.ReversibleResistanceLifetimeTimeChange

@[expose] public section

/-! Measurability and lifetime conventions for the literal physical atomic
clock. Continuous monotone paths are used only on their proved common
almost-sure event. Empty contact families and infinite lifetimes remain
allowed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reversibleResistanceAtomicClock_jointlyMeasurable (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) :
    Measurable (Function.uncurry (reversibleResistanceAtomicClock A x a κ)) := by
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have h := (reversibleResistanceAtomicHazard_jointlyMeasurable A x a κ).comp hm
  have he : Function.uncurry (reversibleResistanceAtomicClock A x a κ) =
      ((fun p : ℝ≥0 × (ℕ → ℝ) => reversibleResistanceAtomicHazard A x a κ p.1 p.2) ∘
        fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) := rfl
  rw [he]
  exact h

theorem reversibleResistanceAtomicClock_measurable (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (t : ℝ) :
    Measurable (reversibleResistanceAtomicClock A x a κ t) := by
  have hm : Measurable (fun ω : ℕ → ℝ => (t, ω)) :=
    measurable_const.prodMk measurable_id
  have h := (reversibleResistanceAtomicClock_jointlyMeasurable A x a κ).comp hm
  change Measurable ((Function.uncurry (reversibleResistanceAtomicClock A x a κ)) ∘
    fun ω : ℕ → ℝ => (t, ω))
  exact h

theorem reversibleResistanceAtomicClock_paths_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ ω ∂brownianDyadicMeasure,
      ContinuousOn (fun t => reversibleResistanceAtomicClock A x a κ t ω) (Ici (0 : ℝ)) ∧
      MonotoneOn (fun t => reversibleResistanceAtomicClock A x a κ t ω) (Ici (0 : ℝ)) := by
  filter_upwards [reversibleResistanceAtomicHazard_paths A x a κ hκ] with ω hω
  exact ⟨(hω.1.comp continuous_real_toNNReal).continuousOn,
    (hω.2.1.comp Real.toNNReal_monotone).monotoneOn _⟩

theorem reversibleResistanceLifetime_eq_attainment_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    contactLifetime (reversibleResistanceAtomicClock A x a κ)
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        reversibleResistanceAttainmentLifetime A x a κ :=
  contactLifetime_eq_attainment_ae brownianDyadicMeasure
    (reversibleResistanceAtomicClock A x a κ)
    (fun t _ => reversibleResistanceAtomicClock_measurable A x a κ t)
    ((reversibleResistanceAtomicClock_paths_ae A x a κ hκ).mono (fun _ hp => hp.2))

theorem reversibleResistanceLifetimeValue_eq_attainment_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    contactLifetimeValue (reversibleResistanceAtomicClock A x a κ)
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        reversibleResistanceAttainmentLifetimeValue A x a κ :=
  contactLifetimeValue_eq_attainment_ae brownianDyadicMeasure
    (reversibleResistanceAtomicClock A x a κ)
    (fun t _ => reversibleResistanceAtomicClock_measurable A x a κ t)
    ((reversibleResistanceAtomicClock_paths_ae A x a κ hκ).mono (fun _ hp => hp.2))

theorem reversibleResistanceAttainmentLifetimeValue_aemeasurable (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    AEMeasurable (reversibleResistanceAttainmentLifetimeValue A x a κ)
      (exponentialKillingMeasure brownianDyadicMeasure) :=
  (contactLifetimeValue_aemeasurable_of_ae_paths brownianDyadicMeasure
    (reversibleResistanceAtomicClock A x a κ)
    (fun t _ => reversibleResistanceAtomicClock_measurable A x a κ t)
    (reversibleResistanceAtomicClock_paths_ae A x a κ hκ)).congr
      (reversibleResistanceLifetimeValue_eq_attainment_ae A x a κ hκ)

end TimeTraps.Probability
