module

public import TimeTraps.Analysis.GraphConservativeSmoothResistance
public import TimeTraps.Graph.TopologicalRealizationMeasurable

@[expose] public section

/-! The resistance coordinate reparametrizes each physical edge without
changing its endpoint identifications or collapsing any interior point. -/

namespace TimeTraps.Graph

open Set

variable {V E : Type*}

noncomputable def MetricGraph.smoothEdgePosition (G : MetricGraph V E) (e : E) (x : ℝ) : ℝ :=
  G.length e * G.smoothResistance e x

theorem MetricGraph.smoothEdgePosition_continuous (G : MetricGraph V E) (e : E) :
    ContinuousOn (G.smoothEdgePosition e) (Icc (0 : ℝ) (G.length e)) :=
  (G.smoothResistance_continuous e).const_mul (G.length e)

theorem MetricGraph.smoothEdgePosition_endpoints (G : MetricGraph V E) (e : E) :
    G.smoothEdgePosition e 0 = 0 ∧ G.smoothEdgePosition e (G.length e) = G.length e := by
  simp only [smoothEdgePosition, (G.smoothResistance_endpoints e).1,
    (G.smoothResistance_endpoints e).2, mul_zero, mul_one, and_self]

theorem MetricGraph.smoothEdgePosition_strictMonoOn (G : MetricGraph V E) (e : E) :
    StrictMonoOn (G.smoothEdgePosition e) (Icc (0 : ℝ) (G.length e)) := by
  intro x hx y hy hxy
  exact mul_lt_mul_of_pos_left (G.smoothResistance_strictMonoOn e hx hy hxy) (G.length_pos e)

theorem MetricGraph.smoothEdgePosition_mem (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (G.length e)) :
    G.smoothEdgePosition e x ∈ Icc (0 : ℝ) (G.length e) := by
  have hs := G.smoothResistance_mem e hx
  exact ⟨mul_nonneg (G.length_pos e).le hs.1,
    (mul_le_mul_of_nonneg_left hs.2 (G.length_pos e).le).trans_eq (mul_one _)⟩

theorem MetricGraph.smoothEdgePosition_endpoint_iff (G : MetricGraph V E) (e : E)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (G.length e)) (v : V) :
    GraphEndpointAt G e (G.smoothEdgePosition e x) v ↔ GraphEndpointAt G e x v := by
  have h0 : G.smoothEdgePosition e x = 0 ↔ x = 0 := by
    simpa only [(G.smoothEdgePosition_endpoints e).1] using
      (G.smoothEdgePosition_strictMonoOn e).injOn.eq_iff hx ⟨le_rfl, (G.length_pos e).le⟩
  have h1 : G.smoothEdgePosition e x = G.length e ↔ x = G.length e := by
    simpa only [(G.smoothEdgePosition_endpoints e).2] using
      (G.smoothEdgePosition_strictMonoOn e).injOn.eq_iff hx ⟨(G.length_pos e).le, le_rfl⟩
  simp only [GraphEndpointAt, h0, h1]

end TimeTraps.Graph
