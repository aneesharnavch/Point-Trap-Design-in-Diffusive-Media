module

public import TimeTraps.Probability.KillingTimeSurvival

@[expose] public section

/-! The actual lifetime as an extended nonnegative random variable.
The value ⊤ is preserved. Measurability follows from the checked survival
events, with no finite-lifetime or finite-mean assumption. -/

namespace TimeTraps.Probability

open Set MeasureTheory
open scoped ENNReal

noncomputable def nonnegativeLifetimeValue (τ : WithTop ℝ) : ℝ≥0∞ :=
  τ.map Real.toNNReal

theorem nonnegativeLifetimeValue_top : nonnegativeLifetimeValue ⊤ = ⊤ := rfl

theorem nonnegativeLifetimeValue_coe (t : ℝ) :
    nonnegativeLifetimeValue (t : WithTop ℝ) = ENNReal.ofReal t := rfl

theorem nonnegativeLifetimeValue_lt_iff (t : ℝ) (ht : 0 ≤ t) (τ : WithTop ℝ) :
    ENNReal.ofReal t < nonnegativeLifetimeValue τ ↔ (t : WithTop ℝ) < τ := by
  induction τ using WithTop.recTopCoe with
  | top => simp only [nonnegativeLifetimeValue_top, ENNReal.ofReal_lt_top, WithTop.coe_lt_top]
  | coe r =>
    rw [nonnegativeLifetimeValue_coe, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht]
    exact WithTop.coe_lt_coe.symm

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def contactLifetimeValue (A : ℝ → Ω → ℝ) (p : Ω × ℝ) : ℝ≥0∞ :=
  nonnegativeLifetimeValue (contactLifetime A p)

theorem contactLifetimeValue_aemeasurable (μ : Measure Ω) (A : ℝ → Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable (A t))
    (hc : ∀ ω, ContinuousOn (fun s => A s ω) (Ici (0 : ℝ)))
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
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
      exact contactLifetime_survival_nullMeasurable μ A (r : ℝ) r.property (hA _ r.property) hc hm
  exact hn.aemeasurable

end TimeTraps.Probability
