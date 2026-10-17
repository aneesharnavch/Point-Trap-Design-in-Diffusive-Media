module

public import TimeTraps.Graph.MetricState

@[expose] public section

/-! The actual normalized resistance coordinate on each original graph
edge is continuous and strictly increasing, and differentiates using
only the reciprocal of the original continuous conductance. -/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis

variable {V E : Type*}

noncomputable def MetricGraph.normalizedResistance (G : MetricGraph V E) (e : E) (x : ℝ) : ℝ :=
  resistancePrimitive (G.conductance e) 0 x / G.resistance e

theorem MetricGraph.normalizedResistance_continuous (G : MetricGraph V E) (e : E) :
    ContinuousOn (G.normalizedResistance e) (Icc (0 : ℝ) (G.length e)) :=
  (resistancePrimitive_continuousOn (G.length_pos e).le (G.conductance_continuous e)
    (fun x hx => (G.conductance_pos e x hx).ne')).div_const (G.resistance e)

theorem MetricGraph.normalizedResistance_hasDerivAt (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (G.length e)) :
    HasDerivAt (G.normalizedResistance e)
      ((1 / G.conductance e x) / G.resistance e) x :=
  (integral_primitive_hasDerivAt
    (continuousOn_const.div (G.conductance_continuous e)
      (fun y hy => (G.conductance_pos e y hy).ne')) hx).div_const (G.resistance e)

theorem MetricGraph.normalizedResistance_endpoints (G : MetricGraph V E) (e : E) :
    G.normalizedResistance e 0 = 0 ∧ G.normalizedResistance e (G.length e) = 1 := by
  constructor
  · simp only [normalizedResistance, resistancePrimitive, intervalIntegral.integral_same, zero_div]
  · exact div_self (G.resistance_pos e).ne'

theorem MetricGraph.normalizedResistance_strictMonoOn (G : MetricGraph V E) (e : E) :
    StrictMonoOn (G.normalizedResistance e) (Icc (0 : ℝ) (G.length e)) := by
  have h := integral_primitive_strictMonoOn (G.length_pos e).le
    (continuousOn_const.div (G.conductance_continuous e)
      (fun y hy => (G.conductance_pos e y hy).ne'))
    (fun y hy => one_div_pos.mpr (G.conductance_pos e y (Ioo_subset_Icc_self hy)))
  intro x hx y hy hxy
  exact (div_lt_div_iff_of_pos_right (G.resistance_pos e)).mpr (h hx hy hxy)

theorem MetricGraph.normalizedResistance_mem (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (G.length e)) :
    G.normalizedResistance e x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← (G.normalizedResistance_endpoints e).1]
    exact (G.normalizedResistance_strictMonoOn e).monotoneOn
      ⟨le_rfl, (G.length_pos e).le⟩ hx hx.1
  · rw [← (G.normalizedResistance_endpoints e).2]
    exact (G.normalizedResistance_strictMonoOn e).monotoneOn
      hx ⟨(G.length_pos e).le, le_rfl⟩ hx.2

theorem MetricGraph.normalizedResistance_mem_interior (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (G.length e)) :
    G.normalizedResistance e x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · rw [← (G.normalizedResistance_endpoints e).1]
    exact G.normalizedResistance_strictMonoOn e
      ⟨le_rfl, (G.length_pos e).le⟩ (Ioo_subset_Icc_self hx) hx.1
  · rw [← (G.normalizedResistance_endpoints e).2]
    exact G.normalizedResistance_strictMonoOn e
      (Ioo_subset_Icc_self hx) ⟨(G.length_pos e).le, le_rfl⟩ hx.2

end TimeTraps.Graph
