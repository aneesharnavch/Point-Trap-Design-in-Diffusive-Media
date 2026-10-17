module

public import TimeTraps.Analysis.GraphHeatPointPotentialBallMeasure
public import Mathlib.Topology.ContinuousMap.Algebra

@[expose] public section

/-! Literal continuous tent functions on the original compact graph.
Their positive ordinary-length integrals derive from the graph measure's
proved positive mass on open sets. -/

namespace TimeTraps.Graph

open Set MeasureTheory

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def MetricGraph.pointTent (G : MetricGraph V E)
    (a : GraphRealization G) (r : ℝ) : C(GraphRealization G, ℝ) :=
  ⟨fun z => max 0 (1 - dist z a / r),
    continuous_const.max (continuous_const.sub ((continuous_id.dist continuous_const).div_const r))⟩

theorem MetricGraph.pointTent_apply (G : MetricGraph V E)
    (a z : GraphRealization G) (r : ℝ) :
    G.pointTent a r z = max 0 (1 - dist z a / r) := rfl

theorem MetricGraph.pointTent_nonneg (G : MetricGraph V E)
    (a z : GraphRealization G) (r : ℝ) : 0 ≤ G.pointTent a r z := le_max_left _ _

theorem MetricGraph.pointTent_le_one (G : MetricGraph V E)
    (a z : GraphRealization G) {r : ℝ} (hr : 0 < r) : G.pointTent a r z ≤ 1 := by
  apply max_le zero_le_one
  have hd : 0 ≤ dist z a / r := div_nonneg dist_nonneg hr.le
  linarith

theorem MetricGraph.pointTent_self (G : MetricGraph V E) (a : GraphRealization G) (r : ℝ) :
    G.pointTent a r a = 1 := by simp only [pointTent_apply, dist_self, zero_div, sub_zero, max_eq_right zero_le_one]

theorem MetricGraph.pointTent_eq_zero (G : MetricGraph V E)
    (a z : GraphRealization G) {r : ℝ} (hr : 0 < r) (hz : r ≤ dist z a) :
    G.pointTent a r z = 0 := by
  have hd : 1 ≤ dist z a / r := (le_div_iff₀ hr).mpr (by simpa)
  exact max_eq_left (by linarith)

theorem MetricGraph.pointTent_support_subset (G : MetricGraph V E)
    (a : GraphRealization G) {r : ℝ} (hr : 0 < r) :
    Function.support (G.pointTent a r) ⊆ Metric.ball a r := by
  intro z hz
  change dist z a < r
  apply lt_of_not_ge
  intro h
  exact hz (G.pointTent_eq_zero a z hr h)

theorem MetricGraph.pointTent_integrable (G : MetricGraph V E)
    (a : GraphRealization G) (r : ℝ) : Integrable (G.pointTent a r) G.lengthMeasure :=
  (G.pointTent a r).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

noncomputable def MetricGraph.pointTentMass (G : MetricGraph V E)
    (a : GraphRealization G) (r : ℝ) : ℝ := ∫ z, G.pointTent a r z ∂G.lengthMeasure

theorem MetricGraph.pointTentMass_pos (G : MetricGraph V E)
    (a : GraphRealization G) (r : ℝ) : 0 < G.pointTentMass a r := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := a) (G.pointTent a r).continuous
    (G.pointTent_integrable a r) (fun z => G.pointTent_nonneg a z r)
  rw [G.pointTent_self]
  exact one_ne_zero

end TimeTraps.Graph
