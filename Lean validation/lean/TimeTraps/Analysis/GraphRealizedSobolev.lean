module

public import TimeTraps.Graph.TopologicalRealizationMeasurable
public import TimeTraps.Analysis.GraphSobolevSpacePhysical

@[expose] public section

/-! Every actual graph H1 state has a unique continuous representative
on the compact graph realization, with the original closed-edge and
shared-vertex values. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Graph

variable {V E : Type*} [Fintype E] [Nonempty E]

omit [Fintype E] in
theorem graphSobolevRepresentative_edge_continuous (G : MetricGraph V E)
    (u : GraphSobolevSpace G) (e : E) :
    Continuous (fun x : Icc (0 : ℝ) (G.length e) => graphSobolevRepresentative G u.val e x.val) := by
  have h := ((graphSobolevSpace_energy G u).edge_energy e).continuousOn
  rw [uIcc_of_le (G.length_pos e).le] at h
  exact h.domRestrict

noncomputable def graphRealizedSobolev (G : MetricGraph V E)
    (u : GraphSobolevSpace G) : C(GraphRealization G, ℝ) :=
  ⟨G.realizationTrace (fun e x => graphSobolevRepresentative G u.val e x.val),
    G.realizationTrace_continuous (graphSobolevNodeValue G u) _
      (graphSobolevRepresentative_edge_continuous G u)
      (graphSobolevSpace_energy G u).tail_value (graphSobolevSpace_energy G u).head_value⟩

theorem graphRealizedSobolev_edge (G : MetricGraph V E) (u : GraphSobolevSpace G)
    (e : E) (x : Icc (0 : ℝ) (G.length e)) :
    graphRealizedSobolev G u (G.edgePoint e x) = graphSobolevRepresentative G u.val e x.val :=
  G.realizationTrace_apply (graphSobolevNodeValue G u)
    (fun e x => graphSobolevRepresentative G u.val e x.val)
    (graphSobolevSpace_energy G u).tail_value (graphSobolevSpace_energy G u).head_value e x

theorem graphRealizedSobolev_ofEnergy (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u)
    (e : E) (x : Icc (0 : ℝ) (G.length e)) :
    graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu) (G.edgePoint e x) = u e x.val :=
  (graphRealizedSobolev_edge G _ e x).trans
    (graphSobolevSpaceOfEnergy_representative G hu e x.property)

theorem graphRealizedSobolev_vertex (G : MetricGraph V E)
    (u : GraphSobolevSpace G) (v : V) :
    graphRealizedSobolev G u (G.vertexPoint v) = graphSobolevNodeValue G u v := by
  obtain ⟨e, he | he⟩ := connected_vertex_incident G.tail G.head G.connected v
  · rw [← he, ← G.edgePoint_tail e, graphRealizedSobolev_edge]
    exact (graphSobolevSpace_energy G u).tail_value e
  · rw [← he, ← G.edgePoint_head e, graphRealizedSobolev_edge]
    exact (graphSobolevSpace_energy G u).head_value e

end TimeTraps.Analysis
