module

public import TimeTraps.Probability.GraphAtomicKillingLifetime
public import TimeTraps.Probability.ExponentialKillingConditionalExpectation

@[expose] public section

/-! Actual graph survival and conditional survival given the whole graph
path. The auxiliary threshold is independent of that path and the closed
first-attainment convention is retained. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetime_survival_probability
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    exponentialKillingMeasure (P.continuousPathLaw h0 x)
      {p | (t : WithTop ℝ) < P.atomicAttainmentLifetime a κ p} =
      ∫⁻ p, ENNReal.ofReal (Real.exp (-P.atomicKillingClock a κ t p)) ∂P.continuousPathLaw h0 x := by
  have he := (P.atomicAttainmentLifetime_survival_iff_ae h0 x a κ hκ t ht).set_eq
  exact (measure_congr he).trans (exponentialKilling_survival _ _
    (P.atomicKillingClock_measurable a κ t) (P.atomicKillingClock_nonneg a κ hκ t))

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetime_indicator_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    ({p | (t : WithTop ℝ) < P.atomicAttainmentLifetime a κ p}.indicator (fun _ => (1 : ℝ)))
      =ᵐ[exponentialKillingMeasure (P.continuousPathLaw h0 x)]
        (exponentialSurvivalEvent (P.atomicKillingClock a κ t)).indicator (fun _ => (1 : ℝ)) := by
  filter_upwards [P.atomicAttainmentLifetime_survival_iff_ae h0 x a κ hκ t ht] with p hp
  simp only [Set.indicator_apply, mem_ofPred_eq, exponentialSurvivalEvent, hp]

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetime_indicator_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    Integrable ({p | (t : WithTop ℝ) < P.atomicAttainmentLifetime a κ p}.indicator (fun _ => (1 : ℝ)))
      (exponentialKillingMeasure (P.continuousPathLaw h0 x)) := by
  let _ := P.continuousPathLaw_probability h0 x
  exact (exponentialKilling_survival_indicator_integrable _ _
    (P.atomicKillingClock_measurable a κ t)).congr
      (P.atomicAttainmentLifetime_indicator_ae h0 x a κ hκ t ht).symm

theorem GraphShiftedContactOperatorProblem.atomicAttainmentLifetime_condExp
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ) (ht : 0 ≤ t) :
    (exponentialKillingMeasure (P.continuousPathLaw h0 x))[
      {p | (t : WithTop ℝ) < P.atomicAttainmentLifetime a κ p}.indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace (GraphContinuousPath P.geometry)).comap
        (Prod.fst : GraphContinuousPath P.geometry × ℝ → GraphContinuousPath P.geometry)]
      =ᵐ[exponentialKillingMeasure (P.continuousPathLaw h0 x)]
        (fun p => Real.exp (-P.atomicKillingClock a κ t p.1)) := by
  let _ := P.continuousPathLaw_probability h0 x
  exact (condExp_congr_ae (P.atomicAttainmentLifetime_indicator_ae h0 x a κ hκ t ht)).trans
    (exponentialKilling_survival_condExp _ _ (P.atomicKillingClock_measurable a κ t)
      (P.atomicKillingClock_nonneg a κ hκ t))

end TimeTraps.Analysis
