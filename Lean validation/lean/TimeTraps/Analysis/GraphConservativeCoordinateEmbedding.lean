module

public import TimeTraps.Analysis.GraphConservativeCoordinateMap

@[expose] public section

/-! The actual resistance coordinates separate every point of the
compact graph, including interiors of loops and parallel edges. -/

namespace TimeTraps.Graph

open Set

variable {V E : Type*} [Nonempty E]

omit [Nonempty E] in
theorem MetricGraph.smoothEdgePoint_fiber (G : MetricGraph V E)
    (e d : E) (x : Icc (0 : ℝ) (G.length e)) (y : Icc (0 : ℝ) (G.length d))
    (h : G.smoothEdgePoint e x = G.smoothEdgePoint d y) :
    G.edgePoint e x = G.edgePoint d y := by
  obtain he | ⟨v, hx, hy⟩ := (G.edgePoint_fiber_iff e d
    ⟨G.smoothEdgePosition e x.val, G.smoothEdgePosition_mem e x.property⟩
    ⟨G.smoothEdgePosition d y.val, G.smoothEdgePosition_mem d y.property⟩).mp h
  · have hed : e = d := congrArg Sigma.fst he
    subst d
    have hp : G.smoothEdgePosition e x.val = G.smoothEdgePosition e y.val :=
      congrArg (fun p : GraphClosedEdgePoint G => p.2.val) he
    have hxy : x = y := Subtype.ext ((G.smoothEdgePosition_strictMonoOn e).injOn x.property y.property hp)
    exact congrArg (G.edgePoint e) hxy
  · exact (G.edgePoint_fiber_iff e d x y).mpr (Or.inr ⟨v,
      (G.smoothEdgePosition_endpoint_iff e x.property v).mp hx,
      (G.smoothEdgePosition_endpoint_iff d y.property v).mp hy⟩)

theorem MetricGraph.smoothRealizationMap_injective (G : MetricGraph V E) :
    Function.Injective G.smoothRealizationMap := by
  intro p q h
  obtain ⟨e, x, rfl⟩ := G.edgePoint_surjective p
  obtain ⟨d, y, rfl⟩ := G.edgePoint_surjective q
  rw [G.smoothRealizationMap_edge, G.smoothRealizationMap_edge] at h
  exact G.smoothEdgePoint_fiber e d x y h

noncomputable def MetricGraph.smoothCoordinates (G : MetricGraph V E) :
    GraphRealization G → GraphRealizationCoordinates V E :=
  fun p => (G.smoothRealizationMap p).val

theorem MetricGraph.smoothCoordinates_injective (G : MetricGraph V E) :
    Function.Injective G.smoothCoordinates := by
  intro p q h
  exact G.smoothRealizationMap_injective (Subtype.ext h)

theorem MetricGraph.smoothCoordinates_continuous [Fintype E] (G : MetricGraph V E) :
    Continuous G.smoothCoordinates := continuous_subtype_val.comp G.smoothRealizationMap_continuous

theorem MetricGraph.smoothCoordinates_edge (G : MetricGraph V E) (e : E)
    (x : Icc (0 : ℝ) (G.length e)) :
    G.smoothCoordinates (G.edgePoint e x) = G.edgeCoordinates e (G.smoothResistance e x.val) := by
  unfold smoothCoordinates
  rw [G.smoothRealizationMap_edge]
  change G.edgeCoordinates e ((G.length e * G.smoothResistance e x.val) / G.length e) = _
  rw [mul_div_cancel_left₀ _ (G.length_pos e).ne']

end TimeTraps.Graph
