module

public import TimeTraps.Probability.GraphContinuousPathReversal
public import TimeTraps.Probability.GraphPhysicalClock

@[expose] public section

/-! The actual Borel speed accumulated through a finite horizon is
unchanged by reversing or stopping the continuous graph path at that
horizon. This is literal interval substitution, without continuity
of the speed across vertices. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem MetricGraph.physicalClock_reverse (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (T : ℝ≥0) (p : GraphContinuousPath G) :
    G.physicalClock b hb T (graphContinuousPathReverse G T p) = G.physicalClock b hb T p := by
  apply NNReal.coe_injective
  rw [G.physicalClock_coe, G.physicalClock_coe]
  change (∫ r in (0 : ℝ)..(T : ℝ), G.physicalSpeed b (p (T - r.toNNReal))) =
    ∫ r in (0 : ℝ)..(T : ℝ), G.physicalSpeed b (p r.toNNReal)
  calc
    _ = ∫ r in (0 : ℝ)..(T : ℝ), G.physicalSpeed b (p ((T : ℝ) - r).toNNReal) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le T.coe_nonneg] at hr
      change G.physicalSpeed b (p (T - r.toNNReal)) = G.physicalSpeed b (p ((T : ℝ) - r).toNNReal)
      apply congrArg (fun t : ℝ≥0 => G.physicalSpeed b (p t))
      apply NNReal.coe_injective
      rw [NNReal.coe_sub (Real.toNNReal_le_iff_le_coe.mpr hr.2),
        Real.coe_toNNReal r hr.1, Real.coe_toNNReal _ (sub_nonneg.mpr hr.2)]
    _ = _ := by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left (fun r : ℝ => G.physicalSpeed b (p r.toNNReal)) (T : ℝ)
          (a := (0 : ℝ)) (b := (T : ℝ)))

theorem MetricGraph.physicalClock_stop (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (T : ℝ≥0) (p : GraphContinuousPath G) :
    G.physicalClock b hb T (graphContinuousPathStop G T p) = G.physicalClock b hb T p := by
  apply NNReal.coe_injective
  rw [G.physicalClock_coe, G.physicalClock_coe]
  change (∫ r in (0 : ℝ)..(T : ℝ), G.physicalSpeed b (p (min r.toNNReal T))) =
    ∫ r in (0 : ℝ)..(T : ℝ), G.physicalSpeed b (p r.toNNReal)
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le T.coe_nonneg] at hr
  change G.physicalSpeed b (p (min r.toNNReal T)) = G.physicalSpeed b (p r.toNNReal)
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hr.2)]

end TimeTraps.Graph
