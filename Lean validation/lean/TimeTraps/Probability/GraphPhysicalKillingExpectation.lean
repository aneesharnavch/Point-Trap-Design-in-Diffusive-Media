module

public import TimeTraps.Probability.GraphAtomicRunningCostInfinite
public import TimeTraps.Probability.GraphPhysicalKillingMean
public import TimeTraps.Probability.GraphPhysicalKillingMeasurable
public import TimeTraps.Probability.ExtendedLifetimeFiniteMean

@[expose] public section

/-! The actual extended physical lifetime has the value of a positive
Dynkin state as its mean. Almost-sure finiteness and an ordinary
integrable real lifetime are consequences, not extra hypotheses. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetimeValue_mean_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ)) (hu : ∀ y, 0 ≤ u y)
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) :
    (∫⁻ p, P.physicalAtomicAttainmentLifetimeValue b hb a κ p
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) = ENNReal.ofReal (u x) :=
  (P.physicalAtomicAttainmentLifetimeValue_mean_identity h0 b hb x a κ hκ).trans
    (P.atomicRunningCost_infinite_of_martingale h0 x b hb a κ hκ u hu hM)

theorem GraphShiftedContactOperatorProblem.physicalAtomicAttainmentLifetime_finite_mean_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ)) (hu : ∀ y, 0 ≤ u y)
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) :
    (∀ᵐ p ∂exponentialKillingMeasure (P.continuousPathLaw h0 x),
      P.physicalAtomicAttainmentLifetime b hb a κ p ≠ ⊤) ∧
    Integrable (fun p => (P.physicalAtomicAttainmentLifetimeValue b hb a κ p).toReal)
      (exponentialKillingMeasure (P.continuousPathLaw h0 x)) ∧
    (∫ p, (P.physicalAtomicAttainmentLifetimeValue b hb a κ p).toReal
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) = u x := by
  have h := extendedLifetime_finite_mean (exponentialKillingMeasure (P.continuousPathLaw h0 x))
    (P.physicalAtomicAttainmentLifetimeValue b hb a κ)
    (P.physicalAtomicAttainmentLifetimeValue_aemeasurable h0 b hb x a κ hκ) (hu x)
    (P.physicalAtomicAttainmentLifetimeValue_mean_of_martingale h0 x b hb a κ hκ u hu hM)
  refine ⟨?_, h.2⟩
  filter_upwards [h.1] with p hp
  intro he
  change nonnegativeLifetimeValue (P.physicalAtomicAttainmentLifetime b hb a κ p) < ⊤ at hp
  rw [he, nonnegativeLifetimeValue_top] at hp
  exact lt_irrefl _ hp

end TimeTraps.Analysis
