module

public import TimeTraps.Probability.GraphPhysicalSpeedData

@[expose] public section

/-! Vertices carry zero ordinary length. Each pushed edge measure is
supported on the open physical edge, which contains no vertex. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped ENNReal BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem MetricGraph.edgePointClamped_eq_openEdge (G : MetricGraph V E) (e : E)
    {r : ℝ} (hr : r ∈ Ioo 0 (G.length e)) :
    G.edgePointClamped e r = G.openEdgePoint e ⟨r, hr⟩ := by
  apply congrArg (G.edgePoint e)
  exact projIcc_of_mem _ ⟨hr.1.le, hr.2.le⟩

theorem MetricGraph.edgeLengthMeasure_vertices (G : MetricGraph V E) (e : E) :
    G.edgeLengthMeasure e (range G.vertexPoint) = 0 := by
  have hS : MeasurableSet (range G.vertexPoint) := (Set.finite_range G.vertexPoint).measurableSet
  rw [edgeLengthMeasure, Measure.map_apply (G.edgePointClamped_measurable e) hS,
    Measure.restrict_apply (hS.preimage (G.edgePointClamped_measurable e))]
  have he : G.edgePointClamped e ⁻¹' range G.vertexPoint ∩ Ioo 0 (G.length e) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro r ⟨⟨v, hv⟩, hr⟩
    exact G.openEdgePoint_ne_vertex e ⟨r, hr⟩ v
      ((G.edgePointClamped_eq_openEdge e hr).symm.trans hv.symm)
  rw [he, measure_empty]

theorem MetricGraph.lengthMeasure_vertices (G : MetricGraph V E) :
    G.lengthMeasure (range G.vertexPoint) = 0 := by
  simp only [lengthMeasure, Measure.finsetSum_apply, G.edgeLengthMeasure_vertices, Finset.sum_const_zero]

end TimeTraps.Graph
