module

public import TimeTraps.Analysis.GraphHeatPointPotentialTent

@[expose] public section

/-! Continuous graph point approximants normalized by their actual
ordinary-length integral. Their unit mass and shrinking support are
proved directly, including centers at graph vertices. -/

namespace TimeTraps.Graph

open Set MeasureTheory

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def MetricGraph.pointBump (G : MetricGraph V E)
    (a : GraphRealization G) (r : ℝ) : C(GraphRealization G, ℝ) :=
  (G.pointTentMass a r)⁻¹ • G.pointTent a r

theorem MetricGraph.pointBump_apply (G : MetricGraph V E)
    (a z : GraphRealization G) (r : ℝ) :
    G.pointBump a r z = (G.pointTentMass a r)⁻¹ * G.pointTent a r z := rfl

theorem MetricGraph.pointBump_nonneg (G : MetricGraph V E)
    (a z : GraphRealization G) (r : ℝ) : 0 ≤ G.pointBump a r z :=
  mul_nonneg (inv_pos.mpr (G.pointTentMass_pos a r)).le (G.pointTent_nonneg a z r)

theorem MetricGraph.pointBump_integrable (G : MetricGraph V E)
    (a : GraphRealization G) (r : ℝ) : Integrable (G.pointBump a r) G.lengthMeasure :=
  (G.pointBump a r).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem MetricGraph.pointBump_integral_one (G : MetricGraph V E)
    (a : GraphRealization G) (r : ℝ) : (∫ z, G.pointBump a r z ∂G.lengthMeasure) = 1 := by
  simp only [pointBump_apply]
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (G.pointTentMass_pos a r).ne'

theorem MetricGraph.pointBump_support_subset (G : MetricGraph V E)
    (a : GraphRealization G) {r : ℝ} (hr : 0 < r) :
    Function.support (G.pointBump a r) ⊆ Metric.ball a r := by
  intro z hz
  apply G.pointTent_support_subset a hr
  intro h
  apply hz
  rw [G.pointBump_apply, h, mul_zero]

theorem MetricGraph.pointBump_tsupport_subset (G : MetricGraph V E)
    (a : GraphRealization G) {r : ℝ} (hr : 0 < r) :
    tsupport (G.pointBump a r) ⊆ Metric.closedBall a r :=
  closure_minimal ((G.pointBump_support_subset a hr).trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall

end TimeTraps.Graph
