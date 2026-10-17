module

public import TimeTraps.Probability.GraphRobinLifetimeExpectation

@[expose] public section

/-! The mean of the actual physical killing lifetime itself belongs to
H1(G) and satisfies the original graph weak equation. This is obtained
from the independently constructed strong state and the actual stochastic
expectation identity, retaining all closed edges and vertex traces. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.physicalMeanLifetime
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (κ : V → ℝ) (x : GraphRealization P.geometry) : ℝ :=
  ∫ p, (P.physicalAtomicAttainmentLifetimeValue b hb (fun v => P.geometry.vertexPoint v) κ p).toReal
    ∂exponentialKillingMeasure (P.continuousPathLaw h0 x)

theorem GraphShiftedContactOperatorProblem.physicalMeanLifetime_weak_equation
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (κ : V → ℝ) (hκ : ∀ v, 0 ≤ κ v) (ha : ∃ v, 0 < κ v) :
    WeakGraphEquation P.geometry κ
      (fun v => P.physicalMeanLifetime h0 b hb κ (P.geometry.vertexPoint v))
      (fun e r => P.physicalMeanLifetime h0 b hb κ (P.geometry.edgePointClamped e r)) := by
  obtain ⟨U, u, j, hj⟩ := graph_state_exists P.geometry κ hκ ha
  have he (e : E) : EqOn (fun r => P.physicalMeanLifetime h0 b hb κ (P.geometry.edgePointClamped e r))
      (u e) (Icc 0 (P.geometry.length e)) := by
    intro r hr
    have h := P.robinWeak_lifetime_mean_edge h0 b hb hj.to_weak hκ ha e ⟨r, hr⟩
    simpa only [GraphShiftedContactOperatorProblem.physicalMeanLifetime,
      MetricGraph.edgePointClamped, projIcc_of_mem (P.geometry.length_pos e).le hr] using h
  have hv (v : V) : P.physicalMeanLifetime h0 b hb κ (P.geometry.vertexPoint v) = U v :=
    P.robinWeak_lifetime_mean_vertex h0 b hb hj.to_weak hκ ha v
  have hs : GraphEquation P.geometry κ
      (fun v => P.physicalMeanLifetime h0 b hb κ (P.geometry.vertexPoint v))
      (fun e r => P.physicalMeanLifetime h0 b hb κ (P.geometry.edgePointClamped e r)) j := by
    refine ⟨fun e => (hj.edge_equation e).congr_state (he e), ?_, ?_, ?_⟩
    · intro e
      exact (he e ⟨le_rfl, (P.geometry.length_pos e).le⟩).trans
        ((hj.tail_value e).trans (hv (P.geometry.tail e)).symm)
    · intro e
      exact (he e ⟨(P.geometry.length_pos e).le, le_rfl⟩).trans
        ((hj.head_value e).trans (hv (P.geometry.head e)).symm)
    · intro v
      rw [hv, hj.vertex_balance]
  exact hs.to_weak

theorem GraphShiftedContactOperatorProblem.physicalMeanLifetime_unique
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation P.geometry κ U u) (hκ : ∀ v, 0 ≤ κ v) (ha : ∃ v, 0 < κ v) :
    (fun v => P.physicalMeanLifetime h0 b hb κ (P.geometry.vertexPoint v)) = U ∧
      ∀ e, EqOn (fun r => P.physicalMeanLifetime h0 b hb κ (P.geometry.edgePointClamped e r))
        (u e) (Icc 0 (P.geometry.length e)) :=
  weak_graph_state_unique (P.physicalMeanLifetime_weak_equation h0 b hb κ hκ ha) hu hκ ha

end TimeTraps.Analysis
