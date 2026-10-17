module

public import TimeTraps.Graph.RealizationLengthMeasure
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! Every open neighborhood in the original compact graph carries
positive ordinary edge length, including neighborhoods of vertices.
This follows directly from a closed-edge representative and the density
of its open physical interval. -/

namespace TimeTraps.Graph

open Set MeasureTheory

variable {V E : Type*} [Fintype V] [Fintype E]

set_option maxHeartbeats 800000

theorem MetricGraph.lengthMeasure_open_pos (G : MetricGraph V E)
    {U : Set (GraphRealization G)} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < G.lengthMeasure U := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨e, u, rfl⟩ := G.edgePoint_surjective p
  let O : Set ℝ := (G.edgePointClamped e) ⁻¹' U
  have hO : IsOpen O := hU.preimage (G.edgePointClamped_continuous e)
  have hu : (u : ℝ) ∈ O := by
    change G.edgePoint e (projIcc 0 (G.length e) (G.length_pos e).le u.val) ∈ U
    simpa only [projIcc_of_mem (G.length_pos e).le u.property] using hp
  have hc : (u : ℝ) ∈ closure (Ioo (0 : ℝ) (G.length e)) := by
    rw [closure_Ioo (G.length_pos e).ne]
    exact u.property
  have hi : (O ∩ Ioo (0 : ℝ) (G.length e)).Nonempty := mem_closure_iff.mp hc O hO hu
  have hv : 0 < volume (O ∩ Ioo (0 : ℝ) (G.length e)) :=
    (hO.inter isOpen_Ioo).measure_pos volume hi
  have he : 0 < G.edgeLengthMeasure e U := by
    rw [MetricGraph.edgeLengthMeasure, Measure.map_apply (G.edgePointClamped_measurable e) hU.measurableSet,
      Measure.restrict_apply (hU.measurableSet.preimage (G.edgePointClamped_measurable e))]
    exact hv
  apply he.trans_le
  rw [MetricGraph.lengthMeasure, Measure.finsetSum_apply]
  exact Finset.single_le_sum (f := fun d => G.edgeLengthMeasure d U)
    (fun _ _ => bot_le) (Finset.mem_univ e)

instance MetricGraph.lengthMeasure_isOpenPos (G : MetricGraph V E) :
    G.lengthMeasure.IsOpenPosMeasure where
  open_pos _U hU hne := (G.lengthMeasure_open_pos hU hne).ne'

theorem MetricGraph.lengthMeasure_ball_pos (G : MetricGraph V E)
    (a : GraphRealization G) {h : ℝ} (hh : 0 < h) :
    0 < G.lengthMeasure (Metric.ball a h) :=
  Metric.isOpen_ball.measure_pos G.lengthMeasure ⟨a, Metric.mem_ball_self hh⟩

theorem MetricGraph.lengthMeasure_ball_real_pos (G : MetricGraph V E)
    (a : GraphRealization G) {h : ℝ} (hh : 0 < h) :
    0 < G.lengthMeasure.real (Metric.ball a h) :=
  ENNReal.toReal_pos (G.lengthMeasure_ball_pos a hh).ne' (measure_ne_top _ _)

end TimeTraps.Graph
