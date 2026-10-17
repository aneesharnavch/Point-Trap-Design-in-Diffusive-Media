module

public import TimeTraps.Analysis.GraphHeatPointPotentialMeasurable
public import TimeTraps.Probability.GraphConservativeOccupationPotentialData

@[expose] public section

/-! Absolute time/space integrability for the literal graph kernel
against a continuous source. The proved one-dimensional envelope supplies
Fubini without an assumed point-potential representation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

theorem GraphShiftedContactOperatorProblem.realizedHeatPointKernel_source_integrable
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (x : GraphRealization P.geometry) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun z : ℝ × GraphRealization P.geometry =>
      P.realizedHeatPointKernelTime x z.2 z.1 * f z.2)
      ((volume.restrict (Ioc 0 T)).prod P.geometry.lengthMeasure) := by
  obtain ⟨C, hC, hb⟩ := P.realizedHeatKernel_global_bound
  have hf : Integrable f P.geometry.lengthMeasure :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := ((shortPointEnvelope_intervalIntegrable hT C).1).mul_prod hf.norm
  have hm : Measurable (fun z : ℝ × GraphRealization P.geometry =>
      P.realizedHeatPointKernelTime x z.2 z.1 * f z.2) :=
    (P.realizedHeatPointKernelTime_jointlyMeasurable.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).mul
        (f.continuous.measurable.comp measurable_snd)
  apply hi.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro z
  rw [norm_mul, Real.norm_eq_abs (P.realizedHeatPointKernelTime x z.2 z.1),
    abs_of_nonneg (P.realizedHeatPointKernelTime_nonneg x z.2 z.1)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  by_cases ht : 0 < z.1
  · unfold realizedHeatPointKernelTime
    rw [dif_pos ht]
    simpa only [Real.coe_toNNReal z.1 ht.le] using
      (hb z.1.toNNReal (Real.toNNReal_pos.mpr ht) x z.2).2
  · simp only [realizedHeatPointKernelTime, dif_neg ht]
    positivity

theorem GraphShiftedContactOperatorProblem.realizedFeller_pointKernel_integral_pos
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (x : GraphRealization P.geometry) {t : ℝ} (ht : 0 < t) :
    P.realizedFeller t.toNNReal f x =
      ∫ y, P.realizedHeatPointKernelTime x y t * f y ∂P.geometry.lengthMeasure := by
  rw [P.realizedFeller_apply, P.realizedTransition_pos t.toNNReal (Real.toNNReal_pos.mpr ht),
    P.realizedHeatTransition_integral]
  simp only [realizedHeatPointKernelTime, dif_pos ht]

end TimeTraps.Analysis
