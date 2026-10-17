module

public import TimeTraps.Graph.RealizationLengthMeasure
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

@[expose] public section

/-! Every open physical edge embeds measurably in the actual graph.
This permits Borel edge data with different traces at shared vertices. -/

namespace TimeTraps.Graph

open Set MeasureTheory

variable {V E : Type*}

noncomputable def MetricGraph.openEdgePoint (G : MetricGraph V E) (e : E)
    (x : Ioo (0 : ℝ) (G.length e)) : GraphRealization G :=
  G.edgePoint e ⟨x.val, x.property.1.le, x.property.2.le⟩

theorem MetricGraph.openEdgePoint_continuous (G : MetricGraph V E) (e : E) :
    Continuous (G.openEdgePoint e) :=
  (G.edgePoint_continuous e).comp (continuous_subtype_val.subtype_mk _)

theorem MetricGraph.openEdgePoint_label (G : MetricGraph V E) (e d : E)
    (x : Ioo (0 : ℝ) (G.length e)) (y : Ioo (0 : ℝ) (G.length d))
    (h : G.openEdgePoint e x = G.openEdgePoint d y) : e = d :=
  congrArg Sigma.fst (G.edgePoint_interior_fiber e d _ _ x.property h)

theorem MetricGraph.openEdgePoint_injective (G : MetricGraph V E) (e : E) :
    Function.Injective (G.openEdgePoint e) := by
  intro x y h
  have he := G.edgePoint_interior_fiber e e _ _ x.property h
  exact Subtype.ext (congrArg (fun z : GraphClosedEdgePoint G => z.2.val) he)

theorem MetricGraph.openEdgePoint_ne_vertex [Nonempty E] (G : MetricGraph V E)
    (e : E) (x : Ioo (0 : ℝ) (G.length e)) (v : V) : G.openEdgePoint e x ≠ G.vertexPoint v := by
  intro h
  have he := (G.closedEdgeCoordinates_vertex_iff e
    ⟨x.val, x.property.1.le, x.property.2.le⟩ v).mp (congrArg Subtype.val h)
  rcases he with ⟨hz, _⟩ | ⟨hl, _⟩
  · exact x.property.1.ne' hz
  · exact x.property.2.ne hl

variable [Fintype V] [Fintype E]

theorem MetricGraph.openEdgePoint_measurableEmbedding (G : MetricGraph V E) (e : E) :
    MeasurableEmbedding (G.openEdgePoint e) := by
  let : PolishSpace (Ioo (0 : ℝ) (G.length e)) := isOpen_Ioo.polishSpace
  exact (G.openEdgePoint_continuous e).measurableEmbedding (G.openEdgePoint_injective e)

theorem MetricGraph.openEdgePoint_range_measurable (G : MetricGraph V E) (e : E) :
    MeasurableSet (range (G.openEdgePoint e)) :=
  (G.openEdgePoint_measurableEmbedding e).measurableSet_range

omit [Fintype V] [Fintype E] in
theorem MetricGraph.point_vertex_or_openEdge [Nonempty E] (G : MetricGraph V E)
    (p : GraphRealization G) : (∃ v, p = G.vertexPoint v) ∨
      ∃ (e : E) (x : Ioo (0 : ℝ) (G.length e)), p = G.openEdgePoint e x := by
  obtain ⟨e, x, rfl⟩ := G.edgePoint_surjective p
  by_cases hz : x.val = 0
  · left
    refine ⟨G.tail e, ?_⟩
    convert G.edgePoint_tail e using 2
    exact Subtype.ext hz
  by_cases hl : x.val = G.length e
  · left
    refine ⟨G.head e, ?_⟩
    convert G.edgePoint_head e using 2
    exact Subtype.ext hl
  · right
    exact ⟨e, ⟨x.val, lt_of_le_of_ne x.property.1 (Ne.symm hz), lt_of_le_of_ne x.property.2 hl⟩, rfl⟩

end TimeTraps.Graph
