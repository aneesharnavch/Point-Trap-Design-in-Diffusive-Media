module

public import TimeTraps.Probability.GraphPhysicalSpeedData

@[expose] public section

/-! The original per-edge source is the physical speed density. Its
arbitrarily fixed vertex value b is explicit; no matching of edge traces
is assumed. The resulting global density is Borel, not asserted continuous. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def MetricGraph.physicalSpeedEdge (G : MetricGraph V E) (b : ℝ) (e : E) :
    GraphRealization G → ℝ :=
  Function.extend (G.openEdgePoint e) (fun x => G.source e x.val - b) (fun _ => 0)

noncomputable def MetricGraph.physicalSpeed (G : MetricGraph V E) (b : ℝ) (p : GraphRealization G) : ℝ :=
  b + ∑ e, G.physicalSpeedEdge b e p

theorem MetricGraph.physicalSpeedEdge_measurable (G : MetricGraph V E) (b : ℝ) (e : E) :
    Measurable (G.physicalSpeedEdge b e) := by
  have hc : Continuous (fun x : Ioo (0 : ℝ) (G.length e) => G.source e x.val) :=
    (G.source_continuous e).comp_continuous continuous_subtype_val
      (fun x => ⟨x.property.1.le, x.property.2.le⟩)
  exact (G.openEdgePoint_measurableEmbedding e).measurable_extend (hc.sub continuous_const).measurable measurable_const

theorem MetricGraph.physicalSpeed_measurable (G : MetricGraph V E) (b : ℝ) :
    Measurable (G.physicalSpeed b) :=
  measurable_const.add (Finset.measurable_sum _ (fun e _ => G.physicalSpeedEdge_measurable b e))

omit [Fintype V] [Fintype E] in
theorem MetricGraph.physicalSpeedEdge_open_self (G : MetricGraph V E) (b : ℝ) (e : E)
    (x : Ioo (0 : ℝ) (G.length e)) :
    G.physicalSpeedEdge b e (G.openEdgePoint e x) = G.source e x.val - b :=
  (G.openEdgePoint_injective e).extend_apply _ _ x

omit [Fintype V] [Fintype E] in
theorem MetricGraph.physicalSpeedEdge_open_other (G : MetricGraph V E) (b : ℝ)
    (e d : E) (hed : e ≠ d) (x : Ioo (0 : ℝ) (G.length d)) :
    G.physicalSpeedEdge b e (G.openEdgePoint d x) = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, hy⟩
  exact hed (G.openEdgePoint_label e d y x hy)

omit [Fintype V] in
theorem MetricGraph.physicalSpeed_openEdge (G : MetricGraph V E) (b : ℝ) (e : E)
    (x : Ioo (0 : ℝ) (G.length e)) :
    G.physicalSpeed b (G.openEdgePoint e x) = G.source e x.val := by
  classical
  unfold physicalSpeed
  rw [Finset.sum_eq_single e]
  · rw [G.physicalSpeedEdge_open_self]
    ring
  · intro d _ hd
    exact G.physicalSpeedEdge_open_other b d e hd x
  · simp

omit [Fintype V] in
theorem MetricGraph.physicalSpeed_vertex [Nonempty E] (G : MetricGraph V E) (b : ℝ) (v : V) :
    G.physicalSpeed b (G.vertexPoint v) = b := by
  unfold physicalSpeed
  suffices (∑ e, G.physicalSpeedEdge b e (G.vertexPoint v)) = 0 by rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro e _
  apply Function.extend_apply'
  rintro ⟨y, hy⟩
  exact G.openEdgePoint_ne_vertex e y v hy

end TimeTraps.Graph
