module

public import TimeTraps.Probability.GraphOccupationL2Data
public import TimeTraps.Probability.BrownianIntegralCompactMaximalTopology

@[expose] public section

/-! The literal time-integrated graph observations as continuous functions
on every compact nonnegative time interval. The source graph paths are
already continuous on every sample, so no exceptional-set replacement is used. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*}

set_option maxHeartbeats 800000

theorem graphOccupation_time_continuous (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (p : GraphContinuousPath G) :
    Continuous (fun t : ℝ≥0 => graphOccupation G f t p) := by
  have hc : Continuous (fun s : ℝ => f (p s.toNNReal)) :=
    f.continuous.comp (p.continuous.comp continuous_real_toNNReal)
  have hp : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, f (p s.toNNReal)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  exact hp.comp NNReal.continuous_coe

noncomputable def graphOccupationCompactPath (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    C(Icc (0 : ℝ≥0) T, ℝ) :=
  ⟨fun t => graphOccupation G f t.val p,
    (graphOccupation_time_continuous G f p).comp continuous_subtype_val⟩

theorem graphOccupationCompactPath_apply (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G)
    (t : Icc (0 : ℝ≥0) T) :
    graphOccupationCompactPath G f T p t = graphOccupation G f t.val p := rfl

theorem graphOccupationCompactPath_zero (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphOccupationCompactPath G f T p ⟨0, by simp⟩ = 0 := by
  simp only [graphOccupationCompactPath_apply, graphOccupation, NNReal.coe_zero,
    intervalIntegral.integral_same]

theorem graphOccupationCompactPath_sub (G : MetricGraph V E)
    (f g : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphOccupationCompactPath G (f - g) T p =
      graphOccupationCompactPath G f T p - graphOccupationCompactPath G g T p := by
  ext t
  change (∫ s in (0 : ℝ)..(t.val : ℝ), (f - g) (p s.toNNReal)) = _
  simp only [ContinuousMap.sub_apply]
  exact intervalIntegral.integral_sub
    ((f.continuous.comp (p.continuous.comp continuous_real_toNNReal)).intervalIntegrable 0 _)
    ((g.continuous.comp (p.continuous.comp continuous_real_toNNReal)).intervalIntegrable 0 _)

end TimeTraps.Analysis
