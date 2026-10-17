module

public import TimeTraps.Analysis.GraphHeatPointPotentialMeasurable

@[expose] public section

/-! Joint continuity in time and both graph points. The zero extension
at negative times permits the parametric primitive theorem across time
zero, dominated by the already proved global graph kernel envelope. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_joint_continuous
    (P : GraphShiftedContactOperatorProblem V E) :
    Continuous (fun z : (GraphRealization P.geometry × GraphRealization P.geometry) × ℝ =>
      P.realizedHeatPointPotential z.1.1 z.1.2 z.2) := by
  obtain ⟨C, hC, hb⟩ := P.realizedHeatKernel_global_bound
  apply continuous_iff_continuousAt.mpr
  intro z
  let M : ℝ := |z.2| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hm (p : GraphRealization P.geometry × GraphRealization P.geometry) :
      AEStronglyMeasurable (P.realizedHeatPointKernelTime p.1 p.2)
        (volume.restrict (Set.uIoc (-M) M)) :=
    (P.realizedHeatPointKernelTime_measurable p.1 p.2).aestronglyMeasurable
  have hbound (p : GraphRealization P.geometry × GraphRealization P.geometry) (t : ℝ) :
      ‖P.realizedHeatPointKernelTime p.1 p.2 t‖ ≤ C * (1 + 1 / Real.sqrt t) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (P.realizedHeatPointKernelTime_nonneg p.1 p.2 t)]
    by_cases ht : 0 < t
    · unfold realizedHeatPointKernelTime
      rw [dif_pos ht]
      simpa only [Real.coe_toNNReal t ht.le] using
        (hb t.toNNReal (Real.toNNReal_pos.mpr ht) p.1 p.2).2
    · simp only [realizedHeatPointKernelTime, dif_neg ht]
      positivity
  have hn : IntervalIntegrable (fun t : ℝ => C * (1 + 1 / Real.sqrt t)) volume (-M) 0 := by
    apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (-M) 0).congr_ae
    rw [uIoc_of_le (neg_nonpos.mpr hM.le)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Real.sqrt_eq_zero_of_nonpos ht.2, div_zero, add_zero, mul_one]
  have hi : IntervalIntegrable (fun t : ℝ => C * (1 + 1 / Real.sqrt t)) volume (-M) M :=
    hn.trans (shortPointEnvelope_intervalIntegrable hM.le C)
  have hzero : (0 : ℝ) ∈ Ioo (-M) M := ⟨by linarith, hM⟩
  have hz : z.2 ∈ Ioo (-M) M := by
    have hlo := neg_abs_le z.2
    have hhi := le_abs_self z.2
    dsimp [M]
    constructor <;> linarith
  exact intervalIntegral.continuousAt_parametric_primitive_of_dominated
    (fun t : ℝ => C * (1 + 1 / Real.sqrt t)) (-M) M hm
    (Eventually.of_forall (fun p => Eventually.of_forall (hbound p))) hi
    (Eventually.of_forall (fun t => (P.realizedHeatPointKernelTime_spatial_continuous t).continuousAt))
    hzero hz (measure_singleton z.2)

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_compact_uniformContinuous
    (P : GraphShiftedContactOperatorProblem V E) (T : ℝ) :
    UniformContinuous (fun z : Icc (0 : ℝ) T ×
      (GraphRealization P.geometry × GraphRealization P.geometry) =>
        P.realizedHeatPointPotential z.2.1 z.2.2 z.1.val) := by
  apply CompactSpace.uniformContinuous_of_continuous
  have hc : Continuous (fun z : Icc (0 : ℝ) T ×
      (GraphRealization P.geometry × GraphRealization P.geometry) => (z.2, z.1.val)) :=
    continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
  have hh := P.realizedHeatPointPotential_joint_continuous.comp hc
  exact hh

end TimeTraps.Analysis
