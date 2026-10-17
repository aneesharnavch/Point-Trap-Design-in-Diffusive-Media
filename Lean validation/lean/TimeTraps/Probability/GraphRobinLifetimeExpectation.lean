module

public import TimeTraps.Probability.GraphPhysicalKillingExpectation
public import TimeTraps.Probability.GraphRobinCompensatedMartingale
public import TimeTraps.Analysis.GraphRobinResolventPositive

@[expose] public section

/-! The original graph H1 weak equation gives the expectation of the
literal physical first-attainment lifetime. Neither a stochastic
martingale identity nor finiteness of lifetime is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.robinWeak_lifetime_mean
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (ha : ∃ v, 0 < κ v) :
    (∫⁻ p, P.physicalAtomicAttainmentLifetimeValue b hb (fun v => P.geometry.vertexPoint v) κ p
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) =
      ENNReal.ofReal (graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) x) :=
  P.physicalAtomicAttainmentLifetimeValue_mean_of_martingale h0 x b hb
    (fun v => P.geometry.vertexPoint v) κ hκ
    (graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy))
    (graphRobinWeak_realized_nonneg hu hκ ha) (P.robinWeak_compensated_martingale h0 x hu b hb)

theorem GraphShiftedContactOperatorProblem.robinWeak_lifetime_finite_mean
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (hκ : ∀ v, 0 ≤ κ v) (ha : ∃ v, 0 < κ v) :
    (∀ᵐ p ∂exponentialKillingMeasure (P.continuousPathLaw h0 x),
      P.physicalAtomicAttainmentLifetime b hb (fun v => P.geometry.vertexPoint v) κ p ≠ ⊤) ∧
    Integrable (fun p => (P.physicalAtomicAttainmentLifetimeValue b hb (fun v => P.geometry.vertexPoint v) κ p).toReal)
      (exponentialKillingMeasure (P.continuousPathLaw h0 x)) ∧
    (∫ p, (P.physicalAtomicAttainmentLifetimeValue b hb (fun v => P.geometry.vertexPoint v) κ p).toReal
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)) =
      graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy) x :=
  P.physicalAtomicAttainmentLifetime_finite_mean_of_martingale h0 x b hb
    (fun v => P.geometry.vertexPoint v) κ hκ
    (graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy))
    (graphRobinWeak_realized_nonneg hu hκ ha) (P.robinWeak_compensated_martingale h0 x hu b hb)

theorem GraphShiftedContactOperatorProblem.robinWeak_lifetime_mean_edge
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation P.geometry κ U u) (hκ : ∀ v, 0 ≤ κ v) (ha : ∃ v, 0 < κ v)
    (e : E) (y : Icc (0 : ℝ) (P.geometry.length e)) :
    (∫ p, (P.physicalAtomicAttainmentLifetimeValue b hb (fun v => P.geometry.vertexPoint v) κ p).toReal
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 (P.geometry.edgePoint e y))) = u e y.val := by
  simpa only [graphRealizedSobolev_ofEnergy] using
    (P.robinWeak_lifetime_finite_mean h0 (P.geometry.edgePoint e y) b hb hu hκ ha).2.2

theorem GraphShiftedContactOperatorProblem.robinWeak_lifetime_mean_vertex
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation P.geometry κ U u) (hκ : ∀ v, 0 ≤ κ v) (ha : ∃ v, 0 < κ v) (v : V) :
    (∫ p, (P.physicalAtomicAttainmentLifetimeValue b hb (fun w => P.geometry.vertexPoint w) κ p).toReal
      ∂exponentialKillingMeasure (P.continuousPathLaw h0 (P.geometry.vertexPoint v))) = U v := by
  simpa only [graphRealizedSobolev_vertex, graphSobolevSpaceOfEnergy_node] using
    (P.robinWeak_lifetime_finite_mean h0 (P.geometry.vertexPoint v) b hb hu hκ ha).2.2

end TimeTraps.Analysis
