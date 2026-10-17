module

public import TimeTraps.Probability.GraphAtomicKillingClock
public import TimeTraps.Probability.KillingLifetimeConventionAE

@[expose] public section

/-! The literal first attainment of an independent unit-exponential
threshold by the actual graph point-local-time clock. The lifetime is
extended-valued: no eventual killing or finite mean is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

noncomputable def GraphShiftedContactOperatorProblem.atomicAttainmentLifetime
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (p : GraphContinuousPath P.geometry × ℝ) : WithTop ℝ :=
  contactAttainmentLifetime (P.atomicKillingClock a κ) p

noncomputable def GraphShiftedContactOperatorProblem.atomicAttainmentLifetimeValue
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (p : GraphContinuousPath P.geometry × ℝ) : ℝ≥0∞ :=
  contactAttainmentLifetimeValue (P.atomicKillingClock a κ) p

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetime_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (p : GraphContinuousPath P.geometry × ℝ) :
    (0 : WithTop ℝ) ≤ P.atomicAttainmentLifetime a κ p :=
  attainmentKillingTime_nonneg _ _

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetime_eq_top_iff
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (p : GraphContinuousPath P.geometry × ℝ) :
    P.atomicAttainmentLifetime a κ p = ⊤ ↔
      ∀ t : ℝ, 0 ≤ t → P.atomicKillingClock a κ t p.1 < p.2 :=
  attainmentKillingTime_eq_top_iff _ _

theorem GraphShiftedContactOperatorProblem.atomicLifetime_eq_attainment_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    contactLifetime (P.atomicKillingClock a κ)
      =ᵐ[exponentialKillingMeasure (P.continuousPathLaw h0 x)] P.atomicAttainmentLifetime a κ :=
  contactLifetime_eq_attainment_ae _ _ (fun t _ => P.atomicKillingClock_measurable a κ t)
    ((P.atomicKillingClock_paths_ae h0 x a κ hκ).mono (fun _ hp => hp.2))

theorem GraphShiftedContactOperatorProblem.atomicLifetimeValue_eq_attainment_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    contactLifetimeValue (P.atomicKillingClock a κ)
      =ᵐ[exponentialKillingMeasure (P.continuousPathLaw h0 x)] P.atomicAttainmentLifetimeValue a κ :=
  contactLifetimeValue_eq_attainment_ae _ _ (fun t _ => P.atomicKillingClock_measurable a κ t)
    ((P.atomicKillingClock_paths_ae h0 x a κ hκ).mono (fun _ hp => hp.2))

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetimeValue_aemeasurable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    AEMeasurable (P.atomicAttainmentLifetimeValue a κ)
      (exponentialKillingMeasure (P.continuousPathLaw h0 x)) :=
  (contactLifetimeValue_aemeasurable_of_ae_paths _ _
    (fun t _ => P.atomicKillingClock_measurable a κ t)
    (P.atomicKillingClock_paths_ae h0 x a κ hκ)).congr
      (P.atomicLifetimeValue_eq_attainment_ae h0 x a κ hκ)

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetime_survival_iff_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ p ∂exponentialKillingMeasure (P.continuousPathLaw h0 x),
      (t : WithTop ℝ) < P.atomicAttainmentLifetime a κ p ↔ P.atomicKillingClock a κ t p.1 < p.2 := by
  filter_upwards [P.atomicLifetime_eq_attainment_ae h0 x a κ hκ,
    contactLifetime_survival_iff_of_ae_paths _ _ t ht (P.atomicKillingClock_measurable a κ t)
      (P.atomicKillingClock_paths_ae h0 x a κ hκ)] with p he hs
  rwa [← he]

end TimeTraps.Analysis
