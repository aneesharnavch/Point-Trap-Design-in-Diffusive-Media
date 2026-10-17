module

public import TimeTraps.Probability.GraphPhysicalClockLaplaceData

@[expose] public section

/-! Joint time/path measurability of both literal Laplace integrands.
The test and the original graph speed are merely Borel measurable. -/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem MetricGraph.physicalPathLaplace_jointlyMeasurable (G : MetricGraph V E)
    (b : ℝ) (hb : 0 < b) {f : GraphRealization G → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable (fun z : ℝ × GraphContinuousPath G =>
      Real.exp (-q * z.1) * f (G.physicalPath b hb z.2 z.1.toNNReal)) := by
  have hT : Measurable (fun z : ℝ × GraphContinuousPath G => (z.1.toNNReal, z.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hX := (G.physicalPath_jointlyMeasurable b hb).comp hT
  have he : Measurable (fun z : ℝ × GraphContinuousPath G => Real.exp (-q * z.1)) := by fun_prop
  exact he.mul (hf.comp hX)

theorem MetricGraph.physicalClockLaplace_jointlyMeasurable (G : MetricGraph V E)
    (b : ℝ) (hb : 0 < b) {f : GraphRealization G → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable (fun z : ℝ × GraphContinuousPath G =>
      Real.exp (-q * (G.physicalClock b hb z.1.toNNReal z.2 : ℝ)) *
        f (z.2 z.1.toNNReal) * G.physicalSpeed b (z.2 z.1.toNNReal)) := by
  have hT : Measurable (fun z : ℝ × GraphContinuousPath G => (z.1.toNNReal, z.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hc := (G.physicalClock_jointlyMeasurable b hb).comp hT
  have hcr : Measurable (fun z : ℝ × GraphContinuousPath G =>
      (G.physicalClock b hb z.1.toNNReal z.2 : ℝ)) := NNReal.continuous_coe.measurable.comp hc
  have hX : Measurable (fun z : ℝ × GraphContinuousPath G => z.2 z.1.toNNReal) := by fun_prop
  exact ((hcr.const_mul (-q)).exp.mul (hf.comp hX)).mul ((G.physicalSpeed_measurable b).comp hX)

end TimeTraps.Graph
