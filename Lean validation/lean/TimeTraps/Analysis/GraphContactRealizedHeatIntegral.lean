module

public import TimeTraps.Analysis.GraphContactRealizedHeatKernel
public import TimeTraps.Analysis.GraphContactHeatKernelIntegral
public import TimeTraps.Graph.RealizationLengthMeasure

@[expose] public section

/-! Physical length integration of the actual variable-conductance heat
kernel on the compact graph. Edge representatives agree almost everywhere
with the same realized kernel, and its total mass is between zero and one. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph InnerProductSpace
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem GraphContactOperatorProblem.realizedHeatKernel_right_continuous
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) : Continuous (P.realizedHeatKernel t ht x) := by
  have hc : Continuous (fun y : GraphRealization P.geometry => (x, y)) :=
    continuous_const.prodMk continuous_id
  have h := (P.realizedHeatKernel_continuous t ht).comp hc
  exact h

theorem GraphContactOperatorProblem.realizedHeatKernel_edge_ae
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    (fun y => P.realizedHeatKernel t ht (P.geometry.edgePoint e x)
      (P.geometry.edgePointClamped d y)) =ᵐ[volume.restrict (Ioo 0 (P.geometry.length d))]
        P.heatKernel t ht e x d := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  change P.realizedHeatKernel t ht (P.geometry.edgePoint e x)
    (P.geometry.edgePoint d (projIcc 0 (P.geometry.length d) (P.geometry.length_pos d).le y)) = _
  rw [P.realizedHeatKernel_edge]
  simp only [projIcc_of_mem (P.geometry.length_pos d).le (Ioo_subset_Icc_self hy)]

theorem GraphContactOperatorProblem.realizedHeatKernel_integrable
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) :
    Integrable (P.realizedHeatKernel t ht x) P.geometry.lengthMeasure :=
  (P.realizedHeatKernel_right_continuous t ht x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem GraphContactOperatorProblem.realizedHeatKernel_edge_mul_integrable
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) (f : GraphL2Product P.geometry) (d : E) :
    Integrable (fun y => P.realizedHeatKernel t ht x (P.geometry.edgePointClamped d y) * (f d) y)
      (volume.restrict (Ioo 0 (P.geometry.length d))) := by
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  apply (P.heatKernel_mul_integrable t ht e u f d).congr
  filter_upwards [P.realizedHeatKernel_edge_ae t ht e d u] with y hy
  rw [hy]

theorem GraphContactOperatorProblem.realizedHeatEvaluation_integral_apply
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) (f : GraphL2Product P.geometry) :
    P.realizedHeatEvaluation t ht x f =
      ∑ d, ∫ y in Ioo 0 (P.geometry.length d),
        P.realizedHeatKernel t ht x (P.geometry.edgePointClamped d y) * (f d) y := by
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  rw [P.realizedHeatEvaluation_edge, P.heatKernel_integral_apply]
  apply Finset.sum_congr rfl
  intro d _
  apply integral_congr_ae
  filter_upwards [P.realizedHeatKernel_edge_ae t ht e d u] with y hy
  rw [hy]

theorem GraphContactOperatorProblem.realizedHeatKernel_mass
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) :
    (∫ y, P.realizedHeatKernel t ht x y ∂P.geometry.lengthMeasure) =
      P.realizedHeatEvaluation t ht x (graphSobolevSpaceStateL P.geometry P.operatorOne) := by
  rw [P.geometry.lengthMeasure_integral _ (P.realizedHeatKernel_right_continuous t ht x),
    P.realizedHeatEvaluation_integral_apply]
  apply Finset.sum_congr rfl
  intro d _
  apply integral_congr_ae
  filter_upwards [P.operatorOne_state_ae d] with y hy
  rw [hy, mul_one]

theorem GraphContactOperatorProblem.realizedHeatKernel_mass_bounds
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) :
    0 ≤ (∫ y, P.realizedHeatKernel t ht x y ∂P.geometry.lengthMeasure) ∧
      (∫ y, P.realizedHeatKernel t ht x y ∂P.geometry.lengthMeasure) ≤ 1 := by
  rw [P.realizedHeatKernel_mass]
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  rw [P.realizedHeatEvaluation_edge, ← P.heatKernel_mass]
  exact P.heatKernel_mass_bounds t ht e u

end TimeTraps.Analysis
