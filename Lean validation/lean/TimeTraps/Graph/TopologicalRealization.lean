module

public import TimeTraps.Graph.MetricState
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! A concrete compact topological realization of the given finite graph.
Vertex coordinates identify precisely the shared endpoint values; two
edge coordinates retain the edge label and orientation inside each edge.
Loops and parallel edges remain distinct in their interiors. Physical edge
lengths enter through the normalized coordinate x / length. -/

namespace TimeTraps.Graph

open Set

variable {V E : Type*}

abbrev GraphRealizationCoordinates (V E : Type*) := (V → ℝ) × (E → ℝ) × (E → ℝ)

noncomputable def graphVertexCoordinates (v : V) : GraphRealizationCoordinates V E := by
  classical
  exact (Pi.single v 1, 0, 0)

noncomputable def MetricGraph.edgeCoordinates (G : MetricGraph V E) (e : E) (s : ℝ) :
    GraphRealizationCoordinates V E := by
  classical
  exact ((1 - s) • Pi.single (G.tail e) 1 + s • Pi.single (G.head e) 1,
    (s * (1 - s)) • Pi.single e 1, (s * (s * (1 - s))) • Pi.single e 1)

theorem MetricGraph.edgeCoordinates_continuous (G : MetricGraph V E) (e : E) :
    Continuous (G.edgeCoordinates e) := by
  classical
  unfold edgeCoordinates
  exact (((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)).prodMk
      (((continuous_id.mul (continuous_const.sub continuous_id)).smul continuous_const).prodMk
        ((continuous_id.mul (continuous_id.mul (continuous_const.sub continuous_id))).smul
          continuous_const))

theorem MetricGraph.edgeCoordinates_zero (G : MetricGraph V E) (e : E) :
    G.edgeCoordinates e 0 = (graphVertexCoordinates (E := E) (G.tail e)) := by
  classical
  simp only [edgeCoordinates, graphVertexCoordinates, sub_zero, one_smul, zero_smul,
    add_zero, zero_mul]

theorem MetricGraph.edgeCoordinates_one (G : MetricGraph V E) (e : E) :
    G.edgeCoordinates e 1 = (graphVertexCoordinates (E := E) (G.head e)) := by
  classical
  simp only [edgeCoordinates, graphVertexCoordinates, sub_self, zero_smul, one_smul,
    zero_add, mul_zero]

abbrev GraphClosedEdgePoint (G : MetricGraph V E) := Σ e : E, Icc (0 : ℝ) (G.length e)

noncomputable def MetricGraph.closedEdgeCoordinates (G : MetricGraph V E)
    (p : GraphClosedEdgePoint G) : GraphRealizationCoordinates V E :=
  G.edgeCoordinates p.1 (p.2.val / G.length p.1)

theorem MetricGraph.closedEdgeCoordinates_continuous (G : MetricGraph V E) :
    Continuous G.closedEdgeCoordinates := by
  apply continuous_sigma
  intro e
  exact (G.edgeCoordinates_continuous e).comp (continuous_subtype_val.div_const (G.length e))

theorem MetricGraph.closedEdgeCoordinates_tail (G : MetricGraph V E) (e : E) :
    G.closedEdgeCoordinates ⟨e, 0, le_rfl, (G.length_pos e).le⟩ =
      (graphVertexCoordinates (E := E) (G.tail e)) := by
  simp only [closedEdgeCoordinates, zero_div, G.edgeCoordinates_zero]

theorem MetricGraph.closedEdgeCoordinates_head (G : MetricGraph V E) (e : E) :
    G.closedEdgeCoordinates ⟨e, G.length e, (G.length_pos e).le, le_rfl⟩ =
      (graphVertexCoordinates (E := E) (G.head e)) := by
  simp only [closedEdgeCoordinates, div_self (G.length_pos e).ne', G.edgeCoordinates_one]

noncomputable def MetricGraph.realizationSet (G : MetricGraph V E) :
    Set (GraphRealizationCoordinates V E) := range G.closedEdgeCoordinates

abbrev GraphRealization (G : MetricGraph V E) := ↥G.realizationSet

theorem MetricGraph.realizationSet_compact [Fintype E] (G : MetricGraph V E) :
    IsCompact G.realizationSet := isCompact_range G.closedEdgeCoordinates_continuous

instance graphRealization_compact [Fintype E] (G : MetricGraph V E) :
    CompactSpace (GraphRealization G) := isCompact_iff_compactSpace.mp G.realizationSet_compact

noncomputable def MetricGraph.edgePoint (G : MetricGraph V E) (e : E)
    (x : Icc (0 : ℝ) (G.length e)) : GraphRealization G :=
  ⟨G.closedEdgeCoordinates ⟨e, x⟩, ⟨⟨e, x⟩, rfl⟩⟩

theorem MetricGraph.edgePoint_continuous (G : MetricGraph V E) (e : E) :
    Continuous (G.edgePoint e) :=
  (G.closedEdgeCoordinates_continuous.comp continuous_sigmaMk).subtype_mk _

theorem MetricGraph.edgePoint_surjective (G : MetricGraph V E) :
    ∀ p : GraphRealization G, ∃ (e : E) (x : Icc (0 : ℝ) (G.length e)), G.edgePoint e x = p := by
  rintro ⟨p, ⟨⟨e, x⟩, hp⟩⟩
  exact ⟨e, x, Subtype.ext hp⟩

end TimeTraps.Graph
