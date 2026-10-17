module

public import TimeTraps.Analysis.GraphHeatPointPotentialContinuity

@[expose] public section

/-! Joint time and spatial measurability of the actual graph heat density,
with its harmless zero value at nonpositive times. This prepares genuine
time/space integration of graph occupation bands. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.realizedHeatPointKernelTime_measurable
    (P : GraphShiftedContactOperatorProblem V E) (x y : GraphRealization P.geometry) :
    Measurable (P.realizedHeatPointKernelTime x y) := by
  classical
  have hm := (P.realizedHeatPointKernelTime_continuousOn x y).measurable_piecewise
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioi (0 : ℝ))ᶜ) measurableSet_Ioi
  have he : (Ioi (0 : ℝ)).piecewise (P.realizedHeatPointKernelTime x y) (fun _ => 0) =
      P.realizedHeatPointKernelTime x y := by
    funext t
    by_cases ht : 0 < t
    · simp only [Set.piecewise, mem_Ioi, if_pos ht]
    · simp only [Set.piecewise, mem_Ioi, if_neg ht, realizedHeatPointKernelTime, dif_neg ht]
  rw [← he]
  exact hm

theorem GraphShiftedContactOperatorProblem.realizedHeatPointKernelTime_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) :
    Measurable (fun z : ℝ × (GraphRealization P.geometry × GraphRealization P.geometry) =>
      P.realizedHeatPointKernelTime z.2.1 z.2.2 z.1) := by
  have hm : Measurable (fun z :
      (GraphRealization P.geometry × GraphRealization P.geometry) × ℝ =>
        P.realizedHeatPointKernelTime z.1.1 z.1.2 z.2) :=
    measurable_uncurry_of_continuous_of_measurable
      (P.realizedHeatPointKernelTime_spatial_continuous)
      (fun z => P.realizedHeatPointKernelTime_measurable z.1 z.2)
  exact hm.comp measurable_swap

end TimeTraps.Analysis
