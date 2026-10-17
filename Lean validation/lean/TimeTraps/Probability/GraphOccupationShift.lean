module

public import TimeTraps.Probability.GraphOccupationShiftData
public import TimeTraps.Probability.GraphLocalTimeCanonicalCocycle

@[expose] public section

/-! The actual time-shift formula for occupation integrals is proved
before passing to local-time limits. It holds for every continuous
spatial profile and every continuous graph path. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*}

theorem graphOccupation_shift (G : MetricGraph V E) (f : C(GraphRealization G, ℝ))
    (p : GraphContinuousPath G) (s t : ℝ≥0) :
    graphOccupation G f t (graphContinuousPathShift G s p) =
      graphOccupation G f (s + t) p - graphOccupation G f s p := by
  have hc : Continuous (fun r : ℝ => f (p r.toNNReal)) :=
    f.continuous.comp (p.continuous.comp continuous_real_toNNReal)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s.val) (hc.intervalIntegrable s.val (s.val + t.val))
  have hs : (∫ r in (0 : ℝ)..t.val, f (p (s + r.toNNReal))) =
      ∫ r in s.val..s.val + t.val, f (p r.toNNReal) := by
    calc
      _ = ∫ r in (0 : ℝ)..t.val, f (p ((s : ℝ) + r).toNNReal) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr0 : 0 ≤ r := (uIcc_of_le t.property ▸ hr).1
        apply congrArg (fun z => f (p z))
        apply NNReal.coe_injective
        change (s : ℝ) + (r.toNNReal : ℝ) = (((s : ℝ) + r).toNNReal : ℝ)
        exact (congrArg (fun z : ℝ => (s : ℝ) + z) (Real.coe_toNNReal r hr0)).trans
          (Real.coe_toNNReal ((s : ℝ) + r) (add_nonneg s.property hr0)).symm
      _ = _ := by
        convert! intervalIntegral.integral_comp_add_left (fun r : ℝ => f (p r.toNNReal))
          (a := 0) (b := t.val) s.val using 1
        simp only [add_zero]
  change (∫ r in (0 : ℝ)..t.val, f (p (s + r.toNNReal))) =
    (∫ r in (0 : ℝ)..(s.val + t.val), f (p r.toNNReal)) -
      (∫ r in (0 : ℝ)..s.val, f (p r.toNNReal))
  rw [hs]
  linarith [hi]

theorem graphOccupation_add (G : MetricGraph V E) (f : C(GraphRealization G, ℝ))
    (p : GraphContinuousPath G) (s t : ℝ≥0) :
    graphOccupation G f (s + t) p = graphOccupation G f s p +
      graphOccupation G f t (graphContinuousPathShift G s p) := by
  rw [graphOccupation_shift]
  ring

theorem graphOccupation_curve_shift (G : MetricGraph V E) (f : C(GraphRealization G, ℝ))
    (p : GraphContinuousPath G) (s : ℝ≥0) :
    (⟨fun t => graphOccupation G f t (graphContinuousPathShift G s p),
      graphOccupation_time_continuous G f (graphContinuousPathShift G s p)⟩ : C(ℝ≥0, ℝ)) =
      continuousPathShift s ⟨fun t => graphOccupation G f t p, graphOccupation_time_continuous G f p⟩ -
        ContinuousMap.const ℝ≥0 (graphOccupation G f s p) := by
  ext t
  exact graphOccupation_shift G f p s t

end TimeTraps.Analysis
