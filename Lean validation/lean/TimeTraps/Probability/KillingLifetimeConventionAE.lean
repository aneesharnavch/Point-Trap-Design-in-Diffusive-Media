module

public import TimeTraps.Probability.KillingLifetimeConvention
public import TimeTraps.Probability.KillingLifetimeMeanAE

@[expose] public section

/-! Independent exponential thresholding removes the distinction between
strict exceedance and first attainment almost surely. Only countably many
rational clock values are excluded. The actual clock is unchanged, its
monotonicity need hold only almost surely, and infinite lifetimes remain
in the equality. This is not an additive-functional or shift theorem. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def contactAttainmentLifetime (A : ℝ → Ω → ℝ) (p : Ω × ℝ) : WithTop ℝ :=
  attainmentKillingTime (fun t => A t p.1) p.2

noncomputable def contactAttainmentLifetimeValue (A : ℝ → Ω → ℝ) (p : Ω × ℝ) : ℝ≥0∞ :=
  nonnegativeLifetimeValue (contactAttainmentLifetime A p)

theorem contactLifetime_eq_attainment_ae (μ : Measure Ω) (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable (A t))
    (hm : ∀ᵐ ω ∂μ, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    contactLifetime A =ᵐ[exponentialKillingMeasure μ] contactAttainmentLifetime A := by
  have hprod : ∀ᵐ p : Ω × ℝ ∂exponentialKillingMeasure μ,
      MonotoneOn (fun s => A s p.1) (Ici (0 : ℝ)) :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := expMeasure 1)).ae hm
  have hrat : ∀ᵐ p : Ω × ℝ ∂exponentialKillingMeasure μ,
      ∀ q : ℚ, 0 ≤ (q : ℝ) → A (q : ℝ) p.1 ≠ p.2 := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 ≤ (q : ℝ)
    · exact (exponentialKilling_threshold_ne μ (A (q : ℝ)) (hA (q : ℝ) hq)).mono
        (fun _ hp _ => hp)
    · exact Eventually.of_forall (fun _ hp => (hq hp).elim)
  filter_upwards [hprod, hrat] with p hp hne
  exact strictKillingTime_eq_attainment_of_rational_ne (fun s => A s p.1) p.2 hp hne

theorem contactLifetimeValue_eq_attainment_ae (μ : Measure Ω) (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable (A t))
    (hm : ∀ᵐ ω ∂μ, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    contactLifetimeValue A =ᵐ[exponentialKillingMeasure μ] contactAttainmentLifetimeValue A := by
  filter_upwards [contactLifetime_eq_attainment_ae μ A hA hm] with p hp
  exact congrArg nonnegativeLifetimeValue hp

end TimeTraps.Probability
