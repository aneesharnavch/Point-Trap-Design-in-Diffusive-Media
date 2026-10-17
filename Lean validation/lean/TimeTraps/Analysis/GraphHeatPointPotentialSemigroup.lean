module

public import TimeTraps.Analysis.GraphHeatPointPotentialSemigroupData

@[expose] public section

/-! The actual Feller occupation potential equals the integral of the
literal point kernel potential against the source. Absolute product
integrability justifies the time/space exchange. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

theorem GraphShiftedContactOperatorProblem.occupationPotential_pointPotential
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (x : GraphRealization P.geometry) {T : ℝ} (hT : 0 ≤ T) :
    P.occupationPotential f T x =
      ∫ y, P.realizedHeatPointPotential x y T * f y ∂P.geometry.lengthMeasure := by
  rw [P.occupationPotential_apply, intervalIntegral.integral_of_le hT]
  calc
    _ = ∫ t in Ioc 0 T, ∫ y, P.realizedHeatPointKernelTime x y t * f y ∂P.geometry.lengthMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact P.realizedFeller_pointKernel_integral_pos f x ht.1
    _ = ∫ y, (∫ t in Ioc (0 : ℝ) T, P.realizedHeatPointKernelTime x y t * f y ∂volume) ∂P.geometry.lengthMeasure :=
      integral_integral_swap (P.realizedHeatPointKernel_source_integrable f x hT)
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      change (∫ t in Ioc (0 : ℝ) T, P.realizedHeatPointKernelTime x y t * f y) =
        P.realizedHeatPointPotential x y T * f y
      rw [integral_mul_const, realizedHeatPointPotential, intervalIntegral.integral_of_le hT]

end TimeTraps.Analysis
