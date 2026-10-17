module

public import TimeTraps.Probability.GraphAtomicKillingSurvival

@[expose] public section

/-! The actual graph lifetime has both layer-cake and path-integrated
survival representations. These are extended expectations and therefore
also cover no trapping and infinite lifetimes. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetimeValue_mean_survival
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, P.atomicAttainmentLifetimeValue a κ p
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ p,
        ENNReal.ofReal (Real.exp (-P.atomicKillingClock a κ t p)) ∂P.continuousPathLaw h0 x := by
  let _ := P.continuousPathLaw_probability h0 x
  exact (lintegral_congr_ae (P.atomicLifetimeValue_eq_attainment_ae h0 x a κ hκ).symm).trans
    (contactLifetime_mean_survival_of_ae_paths _ _
      (fun t _ => P.atomicKillingClock_measurable a κ t)
      (fun t _ => P.atomicKillingClock_nonneg a κ hκ t)
      (P.atomicKillingClock_paths_ae h0 x a κ hκ))

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetimeValue_mean_identity
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    (∫⁻ p, P.atomicAttainmentLifetimeValue a κ p
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) =
      ∫⁻ p, (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-P.atomicKillingClock a κ t p))) ∂P.continuousPathLaw h0 x := by
  let _ := P.continuousPathLaw_probability h0 x
  exact (lintegral_congr_ae (P.atomicLifetimeValue_eq_attainment_ae h0 x a κ hκ).symm).trans
    (contactLifetime_mean_identity_of_ae_paths _ _ (P.atomicKillingClock_jointlyMeasurable a κ)
      (fun t _ => P.atomicKillingClock_nonneg a κ hκ t)
      (P.atomicKillingClock_paths_ae h0 x a κ hκ))

end TimeTraps.Analysis
