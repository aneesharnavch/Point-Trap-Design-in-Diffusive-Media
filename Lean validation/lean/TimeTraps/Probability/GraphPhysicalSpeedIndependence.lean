module

public import TimeTraps.Probability.GraphPhysicalSpeedVertexOccupation
public import TimeTraps.Probability.GraphPhysicalClock

@[expose] public section

/-! The arbitrary positive vertex value does not affect the physical
clock: actual paths spend zero ordinary time at vertices, simultaneously
on the whole positive time axis. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] in
theorem MetricGraph.physicalSpeed_eq_of_not_vertex (G : MetricGraph V E) (b c : ℝ)
    (p : GraphRealization G) (hp : p ∉ range G.vertexPoint) :
    G.physicalSpeed b p = G.physicalSpeed c p := by
  rcases G.point_vertex_or_openEdge p with ⟨v, rfl⟩ | ⟨e, y, rfl⟩
  · exact (hp (mem_range_self v)).elim
  · rw [G.physicalSpeed_openEdge, G.physicalSpeed_openEdge]

end TimeTraps.Graph

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalClock_vertex_value_independent
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (t : ℝ≥0),
      P.geometry.physicalClock b hb t p = P.geometry.physicalClock c hc t p := by
  filter_upwards [P.continuousPathLaw_vertex_time_ae hκ x] with p hp
  intro b c hb hc t
  have he : (∫ r in (0 : ℝ)..(t : ℝ), P.geometry.physicalSpeed b (p r.toNNReal)) =
      ∫ r in (0 : ℝ)..(t : ℝ), P.geometry.physicalSpeed c (p r.toNNReal) := by
    rw [intervalIntegral.integral_of_le t.coe_nonneg, intervalIntegral.integral_of_le t.coe_nonneg]
    apply integral_congr_ae
    exact (ae_restrict_of_ae_restrict_of_subset (fun r hr => hr.1) hp).mono
      (fun r hr => P.geometry.physicalSpeed_eq_of_not_vertex b c _ hr)
  exact NNReal.coe_injective he

theorem GraphShiftedContactOperatorProblem.physicalInverseClock_vertex_value_independent
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (t : ℝ≥0),
      P.geometry.physicalInverseClock b hb t p = P.geometry.physicalInverseClock c hc t p := by
  filter_upwards [P.physicalClock_vertex_value_independent hκ x] with p hp
  intro b c hb hc t
  apply (P.geometry.physicalClock_strictMono c hc p).injective
  dsimp only
  rw [← hp b c hb hc, P.geometry.physicalClock_inverse, P.geometry.physicalClock_inverse]

end TimeTraps.Analysis
