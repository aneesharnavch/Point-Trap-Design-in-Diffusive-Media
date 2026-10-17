module

public import TimeTraps.Probability.GraphPhysicalSpeedBounds
public import TimeTraps.Probability.GraphConservativeNaturalFiltration
public import TimeTraps.Analysis.GraphPhysicalClockInverse

@[expose] public section

/-! The physical clock is the actual integral of the original Borel
edge source along the constructed continuous graph path. Its deterministic
bounds hold for every path, including paths touching vertices. -/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.physicalClockSpeed (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : GraphPhysicalClockSpeed where
  rate t := G.physicalSpeed b (p t)
  measurable_rate := (G.physicalSpeed_measurable b).comp p.continuous.measurable
  lower := G.physicalSpeedLower b hb
  upper := G.physicalSpeedUpper b hb
  lower_pos := G.physicalSpeedLower_pos b hb
  lower_le t := (G.physicalSpeed_bound b hb (p t)).1
  le_upper t := (G.physicalSpeed_bound b hb (p t)).2

noncomputable def MetricGraph.physicalClock (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) (p : GraphContinuousPath G) : ℝ≥0 := (G.physicalClockSpeed b hb p).clock t

noncomputable def MetricGraph.physicalInverseClock (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) (p : GraphContinuousPath G) : ℝ≥0 := (G.physicalClockSpeed b hb p).inverse t

theorem MetricGraph.physicalClock_coe (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) (p : GraphContinuousPath G) :
    (G.physicalClock b hb t p : ℝ) = ∫ r in (0 : ℝ)..t.val, G.physicalSpeed b (p r.toNNReal) := rfl

theorem MetricGraph.physicalClock_zero (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : G.physicalClock b hb 0 p = 0 :=
  (G.physicalClockSpeed b hb p).clock_zero

theorem MetricGraph.physicalClock_continuous (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : Continuous (fun t => G.physicalClock b hb t p) :=
  (G.physicalClockSpeed b hb p).clock_continuous

theorem MetricGraph.physicalClock_strictMono (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : StrictMono (fun t => G.physicalClock b hb t p) :=
  (G.physicalClockSpeed b hb p).clock_strictMono

theorem MetricGraph.physicalClock_bounds (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) (p : GraphContinuousPath G) :
    G.physicalSpeedLower b hb * t ≤ G.physicalClock b hb t p ∧
      G.physicalClock b hb t p ≤ G.physicalSpeedUpper b hb * t :=
  (G.physicalClockSpeed b hb p).clock_bounds t

theorem MetricGraph.physicalClock_inverse (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) (p : GraphContinuousPath G) :
    G.physicalClock b hb (G.physicalInverseClock b hb t p) p = t :=
  (G.physicalClockSpeed b hb p).clock_inverse t

theorem MetricGraph.physicalInverseClock_clock (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) (p : GraphContinuousPath G) :
    G.physicalInverseClock b hb (G.physicalClock b hb t p) p = t :=
  (G.physicalClockSpeed b hb p).inverse_clock t

theorem MetricGraph.physicalInverseClock_bounds (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) (p : GraphContinuousPath G) :
    t / G.physicalSpeedUpper b hb ≤ G.physicalInverseClock b hb t p ∧
      G.physicalInverseClock b hb t p ≤ t / G.physicalSpeedLower b hb :=
  (G.physicalClockSpeed b hb p).inverse_bounds t

end TimeTraps.Graph
