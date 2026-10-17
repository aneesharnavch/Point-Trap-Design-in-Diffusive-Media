module

public import TimeTraps.Graph.TopologicalRealizationFibers

@[expose] public section

/-! Exact endpoint identifications in the concrete graph realization.
The only distinct closed-edge points identified are endpoints attached
to the same original vertex. No interior points are identified. -/

namespace TimeTraps.Graph

open Set

variable {V E : Type*}

def GraphEndpointAt (G : MetricGraph V E) (e : E) (x : ℝ) (v : V) : Prop :=
  (x = 0 ∧ G.tail e = v) ∨ (x = G.length e ∧ G.head e = v)

theorem MetricGraph.edgeCoordinates_vertex_iff (G : MetricGraph V E) (e : E) (s : ℝ) (v : V) :
    G.edgeCoordinates e s = graphVertexCoordinates (E := E) v ↔
      (s = 0 ∧ G.tail e = v) ∨ (s = 1 ∧ G.head e = v) := by
  classical
  constructor
  · intro h
    have hz : s * (1 - s) = 0 := by
      simpa [edgeCoordinates, graphVertexCoordinates] using
        congrArg (fun p : GraphRealizationCoordinates V E => p.2.1 e) h
    rcases mul_eq_zero.mp hz with hs | hs
    · subst s
      exact Or.inl ⟨rfl, graphVertexCoordinates_injective ((G.edgeCoordinates_zero e).symm.trans h)⟩
    · have hs' : s = 1 := by linarith
      subst s
      exact Or.inr ⟨rfl, graphVertexCoordinates_injective ((G.edgeCoordinates_one e).symm.trans h)⟩
  · rintro (⟨rfl, he⟩ | ⟨rfl, he⟩)
    · rw [G.edgeCoordinates_zero, he]
    · rw [G.edgeCoordinates_one, he]

theorem MetricGraph.closedEdgeCoordinates_vertex_iff (G : MetricGraph V E)
    (e : E) (x : Icc (0 : ℝ) (G.length e)) (v : V) :
    G.closedEdgeCoordinates ⟨e, x⟩ = graphVertexCoordinates (E := E) v ↔
      GraphEndpointAt G e x.val v := by
  rw [closedEdgeCoordinates, G.edgeCoordinates_vertex_iff]
  constructor
  · rintro (⟨hx, hv⟩ | ⟨hx, hv⟩)
    · exact Or.inl ⟨by simpa only [zero_mul] using (div_eq_iff (G.length_pos e).ne').mp hx, hv⟩
    · exact Or.inr ⟨by simpa only [one_mul] using (div_eq_iff (G.length_pos e).ne').mp hx, hv⟩
  · rintro (⟨hx, hv⟩ | ⟨hx, hv⟩)
    · exact Or.inl ⟨by rw [hx, zero_div], hv⟩
    · exact Or.inr ⟨by rw [hx, div_self (G.length_pos e).ne'], hv⟩

theorem MetricGraph.closedEdgeCoordinates_fiber_iff (G : MetricGraph V E)
    (e d : E) (x : Icc (0 : ℝ) (G.length e)) (y : Icc (0 : ℝ) (G.length d)) :
    G.closedEdgeCoordinates ⟨e, x⟩ = G.closedEdgeCoordinates ⟨d, y⟩ ↔
      (⟨e, x⟩ : GraphClosedEdgePoint G) = ⟨d, y⟩ ∨
        ∃ v, GraphEndpointAt G e x.val v ∧ GraphEndpointAt G d y.val v := by
  constructor
  · intro h
    by_cases hi : x.val ∈ Ioo (0 : ℝ) (G.length e)
    · exact Or.inl (G.closedEdgeCoordinates_interior_fiber e d x y hi h)
    · have hend : x.val = 0 ∨ x.val = G.length e := by
        by_cases hz : x.val = 0
        · exact Or.inl hz
        · have hp : 0 < x.val := lt_of_le_of_ne x.property.1 (Ne.symm hz)
          exact Or.inr (le_antisymm x.property.2 (not_lt.mp (fun hx => hi ⟨hp, hx⟩)))
      have hex : ∃ v, GraphEndpointAt G e x.val v := by
        rcases hend with hx | hx
        · exact ⟨G.tail e, Or.inl ⟨hx, rfl⟩⟩
        · exact ⟨G.head e, Or.inr ⟨hx, rfl⟩⟩
      obtain ⟨v, hv⟩ := hex
      exact Or.inr ⟨v, hv, (G.closedEdgeCoordinates_vertex_iff d y v).mp
        (h.symm.trans ((G.closedEdgeCoordinates_vertex_iff e x v).mpr hv))⟩
  · rintro (h | ⟨v, hv, hw⟩)
    · exact congrArg G.closedEdgeCoordinates h
    · exact ((G.closedEdgeCoordinates_vertex_iff e x v).mpr hv).trans
        ((G.closedEdgeCoordinates_vertex_iff d y v).mpr hw).symm

theorem MetricGraph.edgePoint_fiber_iff (G : MetricGraph V E)
    (e d : E) (x : Icc (0 : ℝ) (G.length e)) (y : Icc (0 : ℝ) (G.length d)) :
    G.edgePoint e x = G.edgePoint d y ↔
      (⟨e, x⟩ : GraphClosedEdgePoint G) = ⟨d, y⟩ ∨
        ∃ v, GraphEndpointAt G e x.val v ∧ GraphEndpointAt G d y.val v := by
  constructor
  · intro h
    exact (G.closedEdgeCoordinates_fiber_iff e d x y).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((G.closedEdgeCoordinates_fiber_iff e d x y).mpr h)

end TimeTraps.Graph
