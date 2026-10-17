module

public import TimeTraps.Graph.TopologicalRealizationTrace
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! The realized finite graph has its inherited compact metric and Borel
structures. Every original vertex is present when the connected graph has
an edge; physical edge parametrizations are measurable. -/

namespace TimeTraps.Graph

open Set MeasureTheory

variable {V E : Type*}

theorem MetricGraph.vertexCoordinates_mem [Nonempty E] (G : MetricGraph V E) (v : V) :
    graphVertexCoordinates (E := E) v ∈ G.realizationSet := by
  obtain ⟨e, hv | hv⟩ := connected_vertex_incident G.tail G.head G.connected v
  · exact ⟨⟨e, 0, le_rfl, (G.length_pos e).le⟩,
      (G.closedEdgeCoordinates_tail e).trans (congrArg graphVertexCoordinates hv)⟩
  · exact ⟨⟨e, G.length e, (G.length_pos e).le, le_rfl⟩,
      (G.closedEdgeCoordinates_head e).trans (congrArg graphVertexCoordinates hv)⟩

noncomputable def MetricGraph.vertexPoint [Nonempty E] (G : MetricGraph V E) (v : V) :
    GraphRealization G := ⟨graphVertexCoordinates v, G.vertexCoordinates_mem v⟩

theorem MetricGraph.edgePoint_tail [Nonempty E] (G : MetricGraph V E) (e : E) :
    G.edgePoint e ⟨0, le_rfl, (G.length_pos e).le⟩ = G.vertexPoint (G.tail e) :=
  Subtype.ext (G.closedEdgeCoordinates_tail e)

theorem MetricGraph.edgePoint_head [Nonempty E] (G : MetricGraph V E) (e : E) :
    G.edgePoint e ⟨G.length e, (G.length_pos e).le, le_rfl⟩ = G.vertexPoint (G.head e) :=
  Subtype.ext (G.closedEdgeCoordinates_head e)

theorem MetricGraph.vertexPoint_injective [Nonempty E] (G : MetricGraph V E) :
    Function.Injective G.vertexPoint := by
  intro v w h
  exact graphVertexCoordinates_injective (congrArg Subtype.val h)

variable [Fintype V] [Fintype E]

omit [Fintype V] in
theorem MetricGraph.realizationSet_closed (G : MetricGraph V E) : IsClosed G.realizationSet :=
  G.realizationSet_compact.isClosed

instance graphRealization_complete (G : MetricGraph V E) : CompleteSpace (GraphRealization G) :=
  G.realizationSet_closed.completeSpace_coe

instance graphRealization_polish (G : MetricGraph V E) : PolishSpace (GraphRealization G) :=
  G.realizationSet_closed.polishSpace

theorem MetricGraph.edgePoint_measurable (G : MetricGraph V E) (e : E) :
    Measurable (G.edgePoint e) := (G.edgePoint_continuous e).measurable

theorem MetricGraph.realizationMap_measurable (G : MetricGraph V E) :
    Measurable G.realizationMap := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr (fun e => G.edgePoint_measurable e hs)

end TimeTraps.Graph
