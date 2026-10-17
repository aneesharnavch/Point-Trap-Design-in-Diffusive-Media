module

public import TimeTraps.Probability.ReflectedAtomicLifetimeMean

@[expose] public section

/-! Survival of the literal strict-threshold atomic lifetime. The actual
event is null-measurable and its probability is the expected exponential
survival weight. Clock regularity is used only on its proved almost-sure
event; infinite lifetimes remain allowed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι]

theorem reflectedAtomicLifetime_survival_iff_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      (t : WithTop ℝ) < reflectedAtomicLifetime L D x a κ p ↔
        reflectedAtomicClock L D x a κ t p.1 < p.2 :=
  contactLifetime_survival_iff_of_ae_paths brownianDyadicMeasure
    (reflectedAtomicClock L D x a κ) t ht
    (reflectedAtomicClock_measurable L D x a κ t)
    (reflectedAtomicClock_paths_ae L hL D hD x a κ hκ)

theorem reflectedAtomicLifetime_survival_nullMeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (t : ℝ) (ht : 0 ≤ t) :
    NullMeasurableSet {p | (t : WithTop ℝ) < reflectedAtomicLifetime L D x a κ p}
      (exponentialKillingMeasure brownianDyadicMeasure) := by
  have he := (reflectedAtomicLifetime_survival_iff_ae L hL D hD x a κ hκ t ht).set_eq
  exact (exponentialSurvivalEvent_measurable (reflectedAtomicClock L D x a κ t)
    (reflectedAtomicClock_measurable L D x a κ t)).nullMeasurableSet.congr he.symm

theorem reflectedAtomicLifetime_survival_probability (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (t : ℝ) (ht : 0 ≤ t) :
    exponentialKillingMeasure brownianDyadicMeasure
      {p | (t : WithTop ℝ) < reflectedAtomicLifetime L D x a κ p} =
      ENNReal.ofReal (reflectedAtomicMeanSurvival L D x a κ t.toNNReal) := by
  have he : {p | (t : WithTop ℝ) < reflectedAtomicLifetime L D x a κ p}
      =ᵐ[exponentialKillingMeasure brownianDyadicMeasure]
        exponentialSurvivalEvent (reflectedAtomicClock L D x a κ t) :=
    (reflectedAtomicLifetime_survival_iff_ae L hL D hD x a κ hκ t ht).set_eq
  rw [measure_congr he]
  exact (exponentialKilling_survival brownianDyadicMeasure
    (reflectedAtomicClock L D x a κ t) (reflectedAtomicClock_measurable L D x a κ t)
    (fun ω => reflectedAtomicClock_nonneg L hD x a κ hκ t ω)).trans
    (reflectedAtomicSurvival_lintegral L hD x a κ hκ t.toNNReal)

end TimeTraps.Probability
