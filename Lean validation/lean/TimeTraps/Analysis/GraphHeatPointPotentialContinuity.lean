module

public import TimeTraps.Analysis.GraphHeatPointPotentialGlobalIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Joint spatial continuity of the literal graph point potential.
The actual heat kernel is continuous at every positive time, and its
proved integrable bound is uniform in both graph points. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.realizedHeatPointKernelTime_spatial_continuous
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ) :
    Continuous (fun z : GraphRealization P.geometry × GraphRealization P.geometry =>
      P.realizedHeatPointKernelTime z.1 z.2 t) := by
  by_cases ht : 0 < t
  · simpa only [realizedHeatPointKernelTime, dif_pos ht, Function.uncurry_def] using
      P.realizedHeatKernel_continuous t.toNNReal (Real.toNNReal_pos.mpr ht)
  · simp only [realizedHeatPointKernelTime, dif_neg ht]
    exact continuous_const

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_continuous
    (P : GraphShiftedContactOperatorProblem V E) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun z : GraphRealization P.geometry × GraphRealization P.geometry =>
      P.realizedHeatPointPotential z.1 z.2 T) := by
  obtain ⟨C, hC, hb⟩ := P.realizedHeatKernel_global_bound
  have hm (z : GraphRealization P.geometry × GraphRealization P.geometry) :
      AEStronglyMeasurable (P.realizedHeatPointKernelTime z.1 z.2)
        (volume.restrict (Set.uIoc (0 : ℝ) T)) := by
    rw [uIoc_of_le hT]
    exact ((P.realizedHeatPointKernelTime_continuousOn z.1 z.2).mono
      (fun _ ht => ht.1)).aestronglyMeasurable measurableSet_Ioc
  have hbound (z : GraphRealization P.geometry × GraphRealization P.geometry) :
      ∀ᵐ t : ℝ ∂volume, t ∈ Set.uIoc (0 : ℝ) T →
        ‖P.realizedHeatPointKernelTime z.1 z.2 t‖ ≤ C * (1 + 1 / Real.sqrt t) := by
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le hT] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (P.realizedHeatPointKernelTime_nonneg z.1 z.2 t)]
    unfold realizedHeatPointKernelTime
    rw [dif_pos ht.1]
    have h := (hb t.toNNReal (Real.toNNReal_pos.mpr ht.1) z.1 z.2).2
    simpa only [Real.coe_toNNReal t ht.1.le] using h
  exact intervalIntegral.continuous_of_dominated_interval hm hbound
    (shortPointEnvelope_intervalIntegrable hT C)
    (Eventually.of_forall (fun t _ => P.realizedHeatPointKernelTime_spatial_continuous t))

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_uniformContinuous
    (P : GraphShiftedContactOperatorProblem V E) {T : ℝ} (hT : 0 ≤ T) :
    UniformContinuous (fun z : GraphRealization P.geometry × GraphRealization P.geometry =>
      P.realizedHeatPointPotential z.1 z.2 T) :=
  CompactSpace.uniformContinuous_of_continuous (P.realizedHeatPointPotential_continuous hT)

end TimeTraps.Analysis
