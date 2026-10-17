module

public import TimeTraps.Analysis.GraphPhysicalClockRealMeasure
public import TimeTraps.Probability.GraphPhysicalTransitionData

@[expose] public section

/-! Literal pathwise Laplace substitution for the actual physical graph
clock. The speed remains the original bounded Borel function, including
its arbitrary positive representative at vertices. -/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem MetricGraph.physicalClock_jointlyMeasurable (G : MetricGraph V E) (b : ℝ) (hb : 0 < b) :
    Measurable (fun q : ℝ≥0 × GraphContinuousPath G => G.physicalClock b hb q.1 q.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (fun p => G.physicalClock_continuous b hb p)
  intro t
  exact (G.physicalClock_measurable_past b hb t).mono ((graphContinuousNaturalFiltration G).le t) le_rfl

theorem MetricGraph.physicalClock_laplace_path (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (p : GraphContinuousPath G) (f : GraphRealization G → ℝ) (q : ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) * f (G.physicalPath b hb p t.toNNReal)) =
      ∫ s in Ioi (0 : ℝ), Real.exp (-q * (G.physicalClock b hb s.toNNReal p : ℝ)) *
        f (p s.toNNReal) * G.physicalSpeed b (p s.toNNReal) := by
  have hh := (G.physicalClockSpeed b hb p).positive_integral_substitution
    (fun t => Real.exp (-q * (t : ℝ)) * f (G.physicalPath b hb p t))
  calc
    _ = ∫ t in Ioi (0 : ℝ), Real.exp (-q * (t.toNNReal : ℝ)) *
        f (G.physicalPath b hb p t.toNNReal) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.coe_toNNReal t ht.le]
    _ = _ := by
      rw [hh]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro s
      change Real.exp (-q * (G.physicalClock b hb s.toNNReal p : ℝ)) *
        f (G.physicalPath b hb p (G.physicalClock b hb s.toNNReal p)) *
          G.physicalSpeed b (p s.toNNReal) = _
      rw [G.physicalPath_at_clock]

end TimeTraps.Graph
