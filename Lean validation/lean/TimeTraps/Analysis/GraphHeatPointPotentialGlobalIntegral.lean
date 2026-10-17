module

public import TimeTraps.Analysis.GraphHeatPointPotentialGlobal

@[expose] public section

/-! Every finite-time potential of the genuine compact-graph density is
integrable, with a uniform bound supplied by the derived global kernel
estimate. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.realizedHeatPointKernelTime_nonneg
    (P : GraphShiftedContactOperatorProblem V E) (x y : GraphRealization P.geometry) (t : ℝ) :
    0 ≤ P.realizedHeatPointKernelTime x y t := by
  unfold realizedHeatPointKernelTime
  split_ifs with ht
  · exact P.realizedHeatKernel_nonneg _ _ x y
  · exact le_rfl

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_global_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 ≤ T → ∀ (x y : GraphRealization P.geometry),
      IntervalIntegrable (P.realizedHeatPointKernelTime x y) volume 0 T ∧
      0 ≤ P.realizedHeatPointPotential x y T ∧
      P.realizedHeatPointPotential x y T ≤ C * (T + 2 * Real.sqrt T) := by
  obtain ⟨C, hC, hb⟩ := P.realizedHeatKernel_global_bound
  refine ⟨C, hC, ?_⟩
  intro T hT x y
  have hpoint (t : ℝ) (ht : 0 < t) :
      P.realizedHeatPointKernelTime x y t ≤ C * (1 + 1 / Real.sqrt t) := by
    unfold realizedHeatPointKernelTime
    rw [dif_pos ht]
    have h := (hb t.toNNReal (Real.toNNReal_pos.mpr ht) x y).2
    simpa only [Real.coe_toNNReal t ht.le] using h
  have hm : AEStronglyMeasurable (P.realizedHeatPointKernelTime x y)
      (volume.restrict (Set.uIoc (0 : ℝ) T)) := by
    rw [uIoc_of_le hT]
    exact ((P.realizedHeatPointKernelTime_continuousOn x y).mono
      (fun _ ht => ht.1)).aestronglyMeasurable measurableSet_Ioc
  have hi : IntervalIntegrable (P.realizedHeatPointKernelTime x y) volume 0 T := by
    apply (shortPointEnvelope_intervalIntegrable hT C).mono_fun' hm
    rw [uIoc_of_le hT]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (P.realizedHeatPointKernelTime_nonneg x y t)]
    exact hpoint t ht.1
  refine ⟨hi, ?_, ?_⟩
  · exact intervalIntegral.integral_nonneg_of_forall hT (P.realizedHeatPointKernelTime_nonneg x y)
  · calc
      _ ≤ ∫ t in (0 : ℝ)..T, C * (1 + 1 / Real.sqrt t) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hT hi
          (shortPointEnvelope_intervalIntegrable hT C)
        intro t ht
        exact hpoint t ht.1
      _ = _ := shortPointEnvelope_integral hT C

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_symmetric
    (P : GraphShiftedContactOperatorProblem V E) (x y : GraphRealization P.geometry) (T : ℝ) :
    P.realizedHeatPointPotential x y T = P.realizedHeatPointPotential y x T := by
  unfold realizedHeatPointPotential
  congr 1
  funext t
  unfold realizedHeatPointKernelTime
  split_ifs with ht
  · exact P.realizedHeatKernel_symmetric _ _ x y
  · rfl

end TimeTraps.Analysis
