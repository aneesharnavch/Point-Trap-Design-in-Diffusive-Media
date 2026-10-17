module

public import TimeTraps.Analysis.GraphSobolevSpaceNodal
public import TimeTraps.Graph.WeakState

@[expose] public section

/-! Exact correspondence with the original graph energy functions. Every
graph energy function enters the closed trace-matching space; conversely,
when the connected graph has an edge, its nodal values are recovered from
the edge traces, without adding independent nodal coordinates. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*}

theorem graphEndpointTraceL_ofGraphEnergy (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (a : E ⊕ E) :
    graphEndpointTraceL G a (graphSobolevOfEnergy G hu.edge_energy) = U (graphEndpointVertex G a) := by
  cases a with
  | inl e =>
      exact (graphSobolevOfEnergy_representative G hu.edge_energy e
        ⟨le_rfl, (G.length_pos e).le⟩).trans (hu.tail_value e)
  | inr e =>
      exact (graphSobolevOfEnergy_representative G hu.edge_energy e
        ⟨(G.length_pos e).le, le_rfl⟩).trans (hu.head_value e)

noncomputable def graphSobolevSpaceOfEnergy (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) : GraphSobolevSpace G :=
  ⟨graphSobolevOfEnergy G hu.edge_energy, (graphSobolevSubspace_mem_iff G _).mpr (by
    intro a b hab
    rw [graphEndpointTraceL_ofGraphEnergy G hu a, graphEndpointTraceL_ofGraphEnergy G hu b, hab])⟩

theorem graphSobolevSpaceOfEnergy_representative (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (e : E) :
    EqOn (graphSobolevRepresentative G (graphSobolevSpaceOfEnergy G hu).val e) (u e)
      (Icc 0 (G.length e)) := graphSobolevOfEnergy_representative G hu.edge_energy e

theorem graphSobolevSpaceOfEnergy_state_ae (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (e : E) :
    (graphSobolevSpaceStateL G (graphSobolevSpaceOfEnergy G hu)) e
      =ᵐ[volume.restrict (Ioo 0 (G.length e))] u e :=
  graphSobolevOfEnergy_state_ae G hu.edge_energy e

theorem graphSobolevSpace_energy [Nonempty E] (G : MetricGraph V E) (u : GraphSobolevSpace G) :
    GraphEnergy G (graphSobolevNodeValue G u) (graphSobolevRepresentative G u.val) :=
  ⟨graphSobolevRepresentative_energy G u.val,
    fun e => (graphSobolevNodeValue_tail G u e).symm,
    fun e => (graphSobolevNodeValue_head G u e).symm⟩

theorem graphSobolevSpaceOfEnergy_representative_eq [Nonempty E]
    (G : MetricGraph V E) (u : GraphSobolevSpace G) :
    graphSobolevSpaceOfEnergy G (graphSobolevSpace_energy G u) = u := by
  apply Subtype.ext
  exact graphSobolevOfEnergy_representative_eq G u.val

theorem graphSobolevSpace_nodal_unique [Nonempty E] (G : MetricGraph V E)
    (u : GraphSobolevSpace G) {U : V → ℝ}
    (hu : GraphEnergy G U (graphSobolevRepresentative G u.val)) : U = graphSobolevNodeValue G u := by
  funext v
  obtain ⟨e, rfl | rfl⟩ := connected_vertex_incident G.tail G.head G.connected v
  · exact (hu.tail_value e).symm.trans (graphSobolevNodeValue_tail G u e).symm
  · exact (hu.head_value e).symm.trans (graphSobolevNodeValue_head G u e).symm

theorem graphSobolevSpaceOfEnergy_node [Nonempty E] (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (v : V) :
    graphSobolevNodeValue G (graphSobolevSpaceOfEnergy G hu) v = U v := by
  change graphEndpointTraceL G (graphIncidentEndpoint G v)
    (graphSobolevOfEnergy G hu.edge_energy) = U v
  rw [graphEndpointTraceL_ofGraphEnergy G hu (graphIncidentEndpoint G v),
    graphIncidentEndpoint_vertex G v]

end TimeTraps.Analysis
