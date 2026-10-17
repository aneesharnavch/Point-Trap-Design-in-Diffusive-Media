module

public import TimeTraps.Probability.GraphPhysicalClockPath

@[expose] public section

/-! Exact additivity of the physical Borel-speed clock and its inverse.
These pathwise identities retain the original edge speed and require no
continuity of that speed at vertices. -/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem MetricGraph.physicalClock_shift (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (s t : ℝ≥0) :
    (G.physicalClock b hb t (graphContinuousPathShift G s p) : ℝ) =
      (G.physicalClock b hb (s + t) p : ℝ) - (G.physicalClock b hb s p : ℝ) := by
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((G.physicalClockSpeed b hb p).rate_intervalIntegrable 0 s.val)
    ((G.physicalClockSpeed b hb p).rate_intervalIntegrable s.val (s.val + t.val))
  have hs : (∫ r in (0 : ℝ)..t.val, G.physicalSpeed b (p (s + r.toNNReal))) =
      ∫ r in s.val..s.val + t.val, G.physicalSpeed b (p r.toNNReal) := by
    calc
      _ = ∫ r in (0 : ℝ)..t.val, G.physicalSpeed b (p ((s : ℝ) + r).toNNReal) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr0 : 0 ≤ r := (uIcc_of_le t.property ▸ hr).1
        apply congrArg (fun z => G.physicalSpeed b (p z))
        apply NNReal.coe_injective
        change (s : ℝ) + (r.toNNReal : ℝ) = (((s : ℝ) + r).toNNReal : ℝ)
        exact (congrArg (fun z : ℝ => (s : ℝ) + z) (Real.coe_toNNReal r hr0)).trans
          (Real.coe_toNNReal ((s : ℝ) + r) (add_nonneg s.property hr0)).symm
      _ = _ := by
        convert! intervalIntegral.integral_comp_add_left (fun r : ℝ => G.physicalSpeed b (p r.toNNReal))
          (a := 0) (b := t.val) s.val using 1
        simp only [add_zero]
  change (∫ r in (0 : ℝ)..t.val, G.physicalSpeed b (p (s + r.toNNReal))) =
    (∫ r in (0 : ℝ)..(s.val + t.val), G.physicalSpeed b (p r.toNNReal)) -
      (∫ r in (0 : ℝ)..s.val, G.physicalSpeed b (p r.toNNReal))
  rw [hs]
  dsimp only [MetricGraph.physicalClockSpeed] at hi
  linarith [hi]

theorem MetricGraph.physicalClock_add (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (s t : ℝ≥0) :
    G.physicalClock b hb (s + t) p = G.physicalClock b hb s p +
      G.physicalClock b hb t (graphContinuousPathShift G s p) := by
  apply NNReal.coe_injective
  have he := G.physicalClock_shift b hb p s t
  change (G.physicalClock b hb (s + t) p : ℝ) =
    (G.physicalClock b hb s p : ℝ) + (G.physicalClock b hb t (graphContinuousPathShift G s p) : ℝ)
  linarith

theorem MetricGraph.physicalInverseClock_add (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (s t : ℝ≥0) :
    G.physicalInverseClock b hb (s + t) p = G.physicalInverseClock b hb s p +
      G.physicalInverseClock b hb t (graphContinuousPathShift G (G.physicalInverseClock b hb s p) p) := by
  apply (G.physicalClock_strictMono b hb p).injective
  dsimp only
  rw [G.physicalClock_inverse, G.physicalClock_add, G.physicalClock_inverse, G.physicalClock_inverse]

theorem MetricGraph.physicalPath_shift (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (s : ℝ≥0) :
    graphContinuousPathShift G s (G.physicalPath b hb p) =
      G.physicalPath b hb (graphContinuousPathShift G (G.physicalInverseClock b hb s p) p) := by
  apply ContinuousMap.ext
  intro t
  change p (G.physicalInverseClock b hb (s + t) p) =
    p (G.physicalInverseClock b hb s p +
      G.physicalInverseClock b hb t (graphContinuousPathShift G (G.physicalInverseClock b hb s p) p))
  exact congrArg p (G.physicalInverseClock_add b hb p s t)

end TimeTraps.Graph
