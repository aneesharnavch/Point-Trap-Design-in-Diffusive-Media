module

public import TimeTraps.Probability.ReversibleResistanceLifetimeTimeChange

@[expose] public section

/-! Time change preserves the finite-versus-infinite alternative of
the literal lifetime. The statement itself does not assume finiteness;
it transfers any subsequently proved reference finiteness theorem. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

theorem reversibleResistanceAttainmentLifetime_eq_top_iff (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (E : ℝ) :
    reversibleResistanceAttainmentLifetime A x a κ (ω, E) = ⊤ ↔
      reflectedAtomicAttainmentLifetime A.resistanceLength 1 (A.resistance x)
        (fun i => A.resistance (a i)) κ (ω, E) = ⊤ := by
  rw [reversibleResistanceAttainmentLifetime_clock A x a κ hω E, positiveClockLifetimeMap_eq_top_iff]

theorem reversibleResistanceAttainmentLifetime_eq_top_iff_ae (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reversibleResistanceAttainmentLifetime A x a κ p = ⊤ ↔
        reflectedAtomicAttainmentLifetime A.resistanceLength 1 (A.resistance x)
          (fun i => A.resistance (a i)) κ p = ⊤ := by
  filter_upwards [reversibleResistanceAttainmentLifetime_clock_product_ae A x a κ] with p hp
  rw [hp, positiveClockLifetimeMap_eq_top_iff]

theorem reversibleResistanceAttainmentLifetime_ne_top_ae_of_reference (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ)
    (hfinite : ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reflectedAtomicAttainmentLifetime A.resistanceLength 1 (A.resistance x)
        (fun i => A.resistance (a i)) κ p ≠ ⊤) :
    ∀ᵐ p ∂exponentialKillingMeasure brownianDyadicMeasure,
      reversibleResistanceAttainmentLifetime A x a κ p ≠ ⊤ := by
  filter_upwards [reversibleResistanceAttainmentLifetime_eq_top_iff_ae A x a κ, hfinite] with p hp hf
  exact fun h => hf (hp.mp h)

theorem reversibleResistanceAttainmentLifetime_finite_value (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (E r : ℝ)
    (hr : reflectedAtomicAttainmentLifetime A.resistanceLength 1 (A.resistance x)
      (fun i => A.resistance (a i)) κ (ω, E) = (r : WithTop ℝ)) :
    reversibleResistanceAttainmentLifetime A x a κ (ω, E) =
      ((reversibleResistanceClock A x r.toNNReal ω : ℝ) : WithTop ℝ) := by
  rw [reversibleResistanceAttainmentLifetime_clock A x a κ hω E, hr, positiveClockLifetimeMap_coe]

end TimeTraps.Probability
