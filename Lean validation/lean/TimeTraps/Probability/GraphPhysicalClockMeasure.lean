module

public import TimeTraps.Probability.GraphPhysicalClock
public import TimeTraps.Analysis.GraphPhysicalClockIntegral

@[expose] public section

/-! The original graph speed clock has its actual continuous Stieltjes
measure, exactly rho_b(X_s) times ordinary time. This is the physical
clock term used in survival-weighted weak-equation cancellation. -/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.physicalClockStieltjes (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : StieltjesFunction ℝ :=
  (G.physicalClockSpeed b hb p).stieltjes

theorem MetricGraph.physicalClockStieltjes_apply (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (t : ℝ≥0) :
    G.physicalClockStieltjes b hb p (t : ℝ) = (G.physicalClock b hb t p : ℝ) := rfl

theorem MetricGraph.physicalClockStieltjes_continuous (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : Continuous (G.physicalClockStieltjes b hb p) :=
  (G.physicalClockSpeed b hb p).stieltjes_continuous

theorem MetricGraph.physicalClockStieltjes_zero (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) : G.physicalClockStieltjes b hb p 0 = 0 := by
  have he := G.physicalClockStieltjes_apply b hb p 0
  simpa only [NNReal.coe_zero, G.physicalClock_zero] using he

theorem MetricGraph.physicalClockStieltjes_measure (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) :
    (G.physicalClockStieltjes b hb p).measure =
      volume.withDensity (fun r : ℝ => ENNReal.ofReal (G.physicalSpeed b (p r.toNNReal))) :=
  (G.physicalClockSpeed b hb p).stieltjes_measure

theorem MetricGraph.physicalClockStieltjes_weighted_integral (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (w : ℝ≥0 → ℝ) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal ∂(G.physicalClockStieltjes b hb p).measure) =
      ∫ r in Ioc (0 : ℝ) T.val, w r.toNNReal * G.physicalSpeed b (p r.toNNReal) :=
  (G.physicalClockSpeed b hb p).stieltjes_weighted_integral w T

theorem MetricGraph.physicalClockStieltjes_weighted_integrable (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (w : ℝ≥0 → ℝ) (hw : Continuous w) (T : ℝ≥0) :
    IntegrableOn (fun r => w r.toNNReal) (Ioc (0 : ℝ) T.val) (G.physicalClockStieltjes b hb p).measure ∧
      IntegrableOn (fun r => w r.toNNReal * G.physicalSpeed b (p r.toNNReal)) (Ioc (0 : ℝ) T.val) volume :=
  (G.physicalClockSpeed b hb p).stieltjes_weighted_integrable w hw T

end TimeTraps.Graph
