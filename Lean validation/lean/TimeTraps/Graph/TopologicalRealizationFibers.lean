module

public import TimeTraps.Graph.TopologicalRealization

@[expose] public section

/-! The coordinate realization does not collapse any edge interior.
The second and third edge coordinates recover both its label and its
normalized position, including the two orientations of a loop. -/

namespace TimeTraps.Graph

open Set

variable {V E : Type*}

theorem graphVertexCoordinates_injective :
    Function.Injective (graphVertexCoordinates (V := V) (E := E)) := by
  classical
  intro v w h
  by_contra hn
  have he := congrArg (fun p : GraphRealizationCoordinates V E => p.1 v) h
  simp [graphVertexCoordinates, hn] at he

theorem MetricGraph.edgeCoordinates_interior_label (G : MetricGraph V E)
    (e d : E) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (r : ℝ)
    (h : G.edgeCoordinates e s = G.edgeCoordinates d r) : e = d := by
  classical
  by_contra hn
  have he := congrArg (fun p : GraphRealizationCoordinates V E => p.2.1 e) h
  have hp : 0 < s * (1 - s) := mul_pos hs.1 (sub_pos.mpr hs.2)
  have hz : s * (1 - s) = 0 := by
    simpa [edgeCoordinates, Pi.single_apply, hn, Ne.symm hn] using he
  exact hp.ne' hz

theorem MetricGraph.edgeCoordinates_interior_position (G : MetricGraph V E)
    (e : E) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (r : ℝ)
    (h : G.edgeCoordinates e s = G.edgeCoordinates e r) : s = r := by
  classical
  have h₂ : s * (1 - s) = r * (1 - r) := by
    simpa [edgeCoordinates] using congrArg (fun p : GraphRealizationCoordinates V E => p.2.1 e) h
  have h₃ : s * (s * (1 - s)) = r * (r * (1 - r)) := by
    simpa [edgeCoordinates] using congrArg (fun p : GraphRealizationCoordinates V E => p.2.2 e) h
  rw [← h₂] at h₃
  exact mul_right_cancel₀ (mul_pos hs.1 (sub_pos.mpr hs.2)).ne' h₃

theorem MetricGraph.edgeCoordinates_interior_fiber (G : MetricGraph V E)
    (e d : E) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (r : ℝ)
    (h : G.edgeCoordinates e s = G.edgeCoordinates d r) : e = d ∧ s = r := by
  have hed := G.edgeCoordinates_interior_label e d hs r h
  subst d
  exact ⟨rfl, G.edgeCoordinates_interior_position e hs r h⟩

theorem MetricGraph.closedEdgeCoordinates_interior_fiber (G : MetricGraph V E)
    (e d : E) (x : Icc (0 : ℝ) (G.length e)) (y : Icc (0 : ℝ) (G.length d))
    (hx : x.val ∈ Ioo (0 : ℝ) (G.length e))
    (h : G.closedEdgeCoordinates ⟨e, x⟩ = G.closedEdgeCoordinates ⟨d, y⟩) :
    (⟨e, x⟩ : GraphClosedEdgePoint G) = ⟨d, y⟩ := by
  have hs : x.val / G.length e ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hx.1 (G.length_pos e), (div_lt_one (G.length_pos e)).mpr hx.2⟩
  obtain ⟨hed, hxy⟩ := G.edgeCoordinates_interior_fiber e d hs (y.val / G.length d) h
  subst d
  have he : x.val = y.val := by
    calc
      x.val = (x.val / G.length e) * G.length e := (div_mul_cancel₀ _ (G.length_pos e).ne').symm
      _ = (y.val / G.length e) * G.length e := congrArg (fun r : ℝ => r * G.length e) hxy
      _ = y.val := div_mul_cancel₀ _ (G.length_pos e).ne'
  exact congrArg (Sigma.mk e) (Subtype.ext he)

theorem MetricGraph.edgePoint_interior_fiber (G : MetricGraph V E)
    (e d : E) (x : Icc (0 : ℝ) (G.length e)) (y : Icc (0 : ℝ) (G.length d))
    (hx : x.val ∈ Ioo (0 : ℝ) (G.length e)) (h : G.edgePoint e x = G.edgePoint d y) :
    (⟨e, x⟩ : GraphClosedEdgePoint G) = ⟨d, y⟩ :=
  G.closedEdgeCoordinates_interior_fiber e d x y hx (congrArg Subtype.val h)

end TimeTraps.Graph
