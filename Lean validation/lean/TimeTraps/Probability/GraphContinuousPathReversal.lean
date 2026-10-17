module

public import TimeTraps.Probability.GraphOccupationShiftData

@[expose] public section

/-! Literal stopping and reversal of continuous graph trajectories at a
fixed nonnegative horizon. Both maps stay constant after that horizon
and are continuous in the actual compact-open path topology. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped NNReal

variable {V E : Type*}

def graphContinuousPathReverse (G : MetricGraph V E) (T : ℝ≥0) (p : GraphContinuousPath G) :
    GraphContinuousPath G :=
  ⟨fun t => p (T - t), p.continuous.comp (continuous_const.sub continuous_id)⟩

def graphContinuousPathStop (G : MetricGraph V E) (T : ℝ≥0) (p : GraphContinuousPath G) :
    GraphContinuousPath G :=
  ⟨fun t => p (min t T), p.continuous.comp (continuous_id.min continuous_const)⟩

theorem graphContinuousPathReverse_apply (G : MetricGraph V E) (T t : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathReverse G T p t = p (T - t) := rfl

theorem graphContinuousPathStop_apply (G : MetricGraph V E) (T t : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathStop G T p t = p (min t T) := rfl

theorem graphContinuousPathReverse_continuous (G : MetricGraph V E) (T : ℝ≥0) :
    Continuous (graphContinuousPathReverse G T) :=
  (ContinuousMap.uniformContinuous_comp_left
    (⟨fun t : ℝ≥0 => T - t, continuous_const.sub continuous_id⟩ : C(ℝ≥0, ℝ≥0))).continuous

theorem graphContinuousPathStop_continuous (G : MetricGraph V E) (T : ℝ≥0) :
    Continuous (graphContinuousPathStop G T) :=
  (ContinuousMap.uniformContinuous_comp_left
    (⟨fun t : ℝ≥0 => min t T, continuous_id.min continuous_const⟩ : C(ℝ≥0, ℝ≥0))).continuous

theorem graphContinuousPathReverse_measurable [Fintype V] [Fintype E]
    (G : MetricGraph V E) (T : ℝ≥0) : Measurable (graphContinuousPathReverse G T) :=
  (graphContinuousPathReverse_continuous G T).measurable

theorem graphContinuousPathStop_measurable [Fintype V] [Fintype E]
    (G : MetricGraph V E) (T : ℝ≥0) : Measurable (graphContinuousPathStop G T) :=
  (graphContinuousPathStop_continuous G T).measurable

theorem graphContinuousPathReverse_zero (G : MetricGraph V E) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathReverse G T p 0 = p T := by
  simp only [graphContinuousPathReverse_apply, tsub_zero]

theorem graphContinuousPathReverse_horizon (G : MetricGraph V E) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathReverse G T p T = p 0 := by
  simp only [graphContinuousPathReverse_apply, tsub_self]

theorem graphContinuousPathStop_zero (G : MetricGraph V E) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathStop G T p 0 = p 0 := by
  simp only [graphContinuousPathStop_apply, min_eq_left (show (0 : ℝ≥0) ≤ T from zero_le)]

theorem graphContinuousPathStop_horizon (G : MetricGraph V E) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathStop G T p T = p T := by
  simp only [graphContinuousPathStop_apply, min_self]

theorem graphContinuousPathReverse_reverse (G : MetricGraph V E) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathReverse G T (graphContinuousPathReverse G T p) = graphContinuousPathStop G T p := by
  apply ContinuousMap.ext
  intro t
  exact congrArg p ((tsub_tsub_eq_min T t).trans (min_comm T t))

end TimeTraps.Graph
