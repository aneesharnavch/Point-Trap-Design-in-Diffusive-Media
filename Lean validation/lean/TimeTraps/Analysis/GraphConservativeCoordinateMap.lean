module

public import TimeTraps.Analysis.GraphConservativeCoordinatePosition

@[expose] public section

/-! The edgewise resistance reparametrization descends to an actual
continuous map of the compact graph, retaining every original vertex. -/

namespace TimeTraps.Graph

open Set

variable {V E : Type*} [Nonempty E]

noncomputable def MetricGraph.smoothEdgePoint (G : MetricGraph V E) (e : E)
    (x : Icc (0 : ℝ) (G.length e)) : GraphRealization G :=
  G.edgePoint e ⟨G.smoothEdgePosition e x.val, G.smoothEdgePosition_mem e x.property⟩

theorem MetricGraph.smoothEdgePoint_tail (G : MetricGraph V E) (e : E) :
    G.smoothEdgePoint e ⟨0, le_rfl, (G.length_pos e).le⟩ = G.vertexPoint (G.tail e) :=
  (congrArg (G.edgePoint e) (Subtype.ext (G.smoothEdgePosition_endpoints e).1)).trans
    (G.edgePoint_tail e)

theorem MetricGraph.smoothEdgePoint_head (G : MetricGraph V E) (e : E) :
    G.smoothEdgePoint e ⟨G.length e, (G.length_pos e).le, le_rfl⟩ = G.vertexPoint (G.head e) :=
  (congrArg (G.edgePoint e) (Subtype.ext (G.smoothEdgePosition_endpoints e).2)).trans
    (G.edgePoint_head e)

omit [Nonempty E] in
theorem MetricGraph.smoothEdgePoint_continuous (G : MetricGraph V E) (e : E) :
    Continuous (G.smoothEdgePoint e) :=
  (G.edgePoint_continuous e).comp ((G.smoothEdgePosition_continuous e).domRestrict.subtype_mk _)

noncomputable def MetricGraph.smoothRealizationMap (G : MetricGraph V E) :
    GraphRealization G → GraphRealization G := G.realizationTrace G.smoothEdgePoint

theorem MetricGraph.smoothRealizationMap_edge (G : MetricGraph V E) (e : E)
    (x : Icc (0 : ℝ) (G.length e)) :
    G.smoothRealizationMap (G.edgePoint e x) = G.smoothEdgePoint e x :=
  G.realizationTrace_apply G.vertexPoint G.smoothEdgePoint G.smoothEdgePoint_tail G.smoothEdgePoint_head e x

theorem MetricGraph.smoothRealizationMap_continuous [Fintype E] (G : MetricGraph V E) :
    Continuous G.smoothRealizationMap :=
  G.realizationTrace_continuous G.vertexPoint G.smoothEdgePoint G.smoothEdgePoint_continuous
    G.smoothEdgePoint_tail G.smoothEdgePoint_head

end TimeTraps.Graph
