module

public import TimeTraps.Analysis.GraphContactHeatKernelIntegral

@[expose] public section

/-! The physical graph kernel satisfies the exact positive-time
composition law. All edge integrals use ordinary length measure;
their existence follows from the actual edge L2 representatives. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphContactOperatorProblem.heatSobolevL_continuousOn (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (f : GraphL2Product P.geometry) (d : E) :
    ContinuousOn (P.operatorRep (P.heatSobolevL t ht f) d) (Icc 0 (P.geometry.length d)) := by
  have h := (P.operatorRep_energy (P.heatSobolevL t ht f)).edge_energy d |>.continuousOn
  change ContinuousOn (P.operatorRep (P.heatSobolevL t ht f) d) (uIcc 0 (P.geometry.length d)) at h
  simpa only [uIcc_of_le (P.geometry.length_pos d).le] using h

theorem GraphContactOperatorProblem.heatKernel_continuousOn_right (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) (d : E) :
    ContinuousOn (P.heatKernel t ht e x d) (Icc 0 (P.geometry.length d)) :=
  P.heatSobolevL_continuousOn (t / 2) (div_pos ht (by norm_num)) _ d

theorem GraphContactOperatorProblem.heatKernel_split (P : GraphContactOperatorProblem V E)
    (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (e d : E)
    (x : Icc (0 : ℝ) (P.geometry.length e)) (y : Icc (0 : ℝ) (P.geometry.length d)) :
    P.heatKernel (s + t) (add_pos hs ht) e x d y =
      P.heatPointEvaluation t ht d y (P.heatKernelVector s hs e x) := by
  have hrep := P.heatKernel_representative (s + t) (add_pos hs ht) e x d
  rw [P.heatKernelVector_add s hs t e x] at hrep
  have he := hrep.symm.trans (P.heatSobolevL_state_ae t ht (P.heatKernelVector s hs e x) d)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at he
  exact Measure.eqOn_Icc_of_ae_eq volume (P.geometry.length_pos d).ne he
    (P.heatKernel_continuousOn_right (s + t) (add_pos hs ht) e x d)
    (P.heatSobolevL_continuousOn t ht (P.heatKernelVector s hs e x) d) y.property

theorem GraphContactOperatorProblem.heatKernel_split_inner (P : GraphContactOperatorProblem V E)
    (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (e d : E)
    (x : Icc (0 : ℝ) (P.geometry.length e)) (y : Icc (0 : ℝ) (P.geometry.length d)) :
    P.heatKernel (s + t) (add_pos hs ht) e x d y =
      inner ℝ (P.heatKernelVector s hs e x) (P.heatKernelVector t ht d y) := by
  rw [P.heatKernel_split s t hs ht e d x y]
  exact (P.heatKernelVector_inner t ht d y _).symm.trans (real_inner_comm _ _)

theorem GraphContactOperatorProblem.heatKernel_product_integrable (P : GraphContactOperatorProblem V E)
    (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (e d : E)
    (x : Icc (0 : ℝ) (P.geometry.length e)) (y : Icc (0 : ℝ) (P.geometry.length d)) (b : E) :
    Integrable (fun z => P.heatKernel s hs e x b z * P.heatKernel t ht d y b z)
      (volume.restrict (Ioo 0 (P.geometry.length b))) := by
  apply (P.heatKernel_mul_integrable s hs e x (P.heatKernelVector t ht d y) b).congr
  filter_upwards [P.heatKernel_representative t ht d y b] with z hz
  rw [hz]

theorem GraphContactOperatorProblem.heatKernel_composition (P : GraphContactOperatorProblem V E)
    (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (e d : E)
    (x : Icc (0 : ℝ) (P.geometry.length e)) (y : Icc (0 : ℝ) (P.geometry.length d)) :
    P.heatKernel (s + t) (add_pos hs ht) e x d y =
      ∑ b, ∫ z in Ioo 0 (P.geometry.length b),
        P.heatKernel s hs e x b z * P.heatKernel t ht d y b z := by
  rw [P.heatKernel_split_inner s t hs ht e d x y, graphL2Product_inner]
  apply Finset.sum_congr rfl
  intro b _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [P.heatKernel_representative s hs e x b,
    P.heatKernel_representative t ht d y b] with z hz hw
  simp only [Real.inner_apply, hz, hw]

end TimeTraps.Analysis
