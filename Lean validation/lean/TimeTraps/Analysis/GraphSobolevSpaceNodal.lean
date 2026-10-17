module

public import TimeTraps.Analysis.GraphSobolevSpace
public import TimeTraps.Analysis.GraphSobolevProductPhysical

@[expose] public section

/-! On a connected graph with a nonempty edge set, each vertex is incident
to an endpoint. Its value is then a bounded trace of the actual edge H1
state, independent of which incident endpoint is selected. -/

namespace TimeTraps.Analysis

open TimeTraps.Graph

variable {V E : Type*} [Nonempty E]

theorem graphEndpointVertex_surjective (G : MetricGraph V E) :
    Function.Surjective (graphEndpointVertex G) := by
  intro v
  obtain ⟨e, h | h⟩ := connected_vertex_incident G.tail G.head G.connected v
  · exact ⟨.inl e, h⟩
  · exact ⟨.inr e, h⟩

noncomputable def graphIncidentEndpoint (G : MetricGraph V E) (v : V) : E ⊕ E :=
  Classical.choose (graphEndpointVertex_surjective G v)

theorem graphIncidentEndpoint_vertex (G : MetricGraph V E) (v : V) :
    graphEndpointVertex G (graphIncidentEndpoint G v) = v :=
  Classical.choose_spec (graphEndpointVertex_surjective G v)

noncomputable def graphSobolevNodeValueL (G : MetricGraph V E) (v : V) :
    GraphSobolevSpace G →L[ℝ] ℝ :=
  (graphEndpointTraceL G (graphIncidentEndpoint G v)).comp (graphSobolevSubspace G).subtypeL

noncomputable def graphSobolevNodeValue (G : MetricGraph V E)
    (u : GraphSobolevSpace G) (v : V) : ℝ := graphSobolevNodeValueL G v u

theorem graphSobolevNodeValue_endpoint (G : MetricGraph V E)
    (u : GraphSobolevSpace G) (a : E ⊕ E) :
    graphSobolevNodeValue G u (graphEndpointVertex G a) = graphEndpointTraceL G a u.val :=
  (graphSobolevSubspace_mem_iff G u.val).mp u.property _ _
    (graphIncidentEndpoint_vertex G (graphEndpointVertex G a))

theorem graphSobolevNodeValue_tail (G : MetricGraph V E)
    (u : GraphSobolevSpace G) (e : E) :
    graphSobolevNodeValue G u (G.tail e) = graphSobolevRepresentative G u.val e 0 :=
  graphSobolevNodeValue_endpoint G u (.inl e)

theorem graphSobolevNodeValue_head (G : MetricGraph V E)
    (u : GraphSobolevSpace G) (e : E) :
    graphSobolevNodeValue G u (G.head e) =
      graphSobolevRepresentative G u.val e (G.length e) :=
  graphSobolevNodeValue_endpoint G u (.inr e)

end TimeTraps.Analysis
