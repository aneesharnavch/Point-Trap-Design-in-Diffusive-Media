module

public import TimeTraps.Probability.GraphOccupationCompactData

@[expose] public section

/-! Literal time shifts of continuous graph paths. These are continuous
Borel maps on the actual compact-open path space and satisfy the shift
semigroup identities pointwise. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped NNReal

variable {V E : Type*}

def graphContinuousPathShift (G : MetricGraph V E) (s : ℝ≥0) (p : GraphContinuousPath G) :
    GraphContinuousPath G :=
  ⟨fun t => p (s + t), p.continuous.comp (continuous_const.add continuous_id)⟩

theorem graphContinuousPathShift_apply (G : MetricGraph V E) (s t : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathShift G s p t = p (s + t) := rfl

theorem graphContinuousPathShift_continuous (G : MetricGraph V E) (s : ℝ≥0) :
    Continuous (graphContinuousPathShift G s) :=
  (ContinuousMap.uniformContinuous_comp_left
    (⟨fun t : ℝ≥0 => s + t, continuous_const.add continuous_id⟩ : C(ℝ≥0, ℝ≥0))).continuous

theorem graphContinuousPathShift_measurable [Fintype V] [Fintype E]
    (G : MetricGraph V E) (s : ℝ≥0) : Measurable (graphContinuousPathShift G s) :=
  (graphContinuousPathShift_continuous G s).measurable

theorem graphContinuousPathShift_zero (G : MetricGraph V E) (p : GraphContinuousPath G) :
    graphContinuousPathShift G 0 p = p := by
  apply ContinuousMap.ext
  intro t
  exact congrArg p (zero_add t)

theorem graphContinuousPathShift_add (G : MetricGraph V E) (s t : ℝ≥0) (p : GraphContinuousPath G) :
    graphContinuousPathShift G t (graphContinuousPathShift G s p) =
      graphContinuousPathShift G (s + t) p := by
  apply ContinuousMap.ext
  intro r
  exact congrArg p (add_assoc s t r).symm

end TimeTraps.Graph
