module

public import TimeTraps.Analysis.GraphContactRealizedHeat
public import TimeTraps.Analysis.GraphContactHeatKernel

@[expose] public section

/-! The actual positive-time heat kernel on the compact graph realization.
The two variable kernel agrees exactly with the original physical edge
kernel, including at shared vertices. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphContactOperatorProblem.realizedHeatKernel (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (x y : GraphRealization P.geometry) : ℝ :=
  inner ℝ (P.realizedHeatVector (t / 2) (div_pos ht (by norm_num)) x)
    (P.realizedHeatVector (t / 2) (div_pos ht (by norm_num)) y)

theorem GraphContactOperatorProblem.realizedHeatKernel_edge (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E)
    (x : Icc (0 : ℝ) (P.geometry.length e)) (y : Icc (0 : ℝ) (P.geometry.length d)) :
    P.realizedHeatKernel t ht (P.geometry.edgePoint e x) (P.geometry.edgePoint d y) =
      P.heatKernel t ht e x d y := by
  unfold realizedHeatKernel
  rw [P.realizedHeatVector_edge, P.realizedHeatVector_edge]
  exact (P.heatKernel_eq_inner t ht e d x y).symm

theorem GraphContactOperatorProblem.realizedHeatKernel_continuous (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) : Continuous (Function.uncurry (P.realizedHeatKernel t ht)) :=
  ((P.realizedHeatVector_continuous (t / 2) (div_pos ht (by norm_num))).comp continuous_fst).inner
    ((P.realizedHeatVector_continuous (t / 2) (div_pos ht (by norm_num))).comp continuous_snd)

theorem GraphContactOperatorProblem.realizedHeatKernel_measurable (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) : Measurable (Function.uncurry (P.realizedHeatKernel t ht)) :=
  (P.realizedHeatKernel_continuous t ht).measurable

theorem GraphContactOperatorProblem.realizedHeatKernel_symmetric (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (x y : GraphRealization P.geometry) :
    P.realizedHeatKernel t ht x y = P.realizedHeatKernel t ht y x := real_inner_comm _ _

theorem GraphContactOperatorProblem.realizedHeatKernel_nonneg (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (x y : GraphRealization P.geometry) :
    0 ≤ P.realizedHeatKernel t ht x y := by
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  obtain ⟨d, v, rfl⟩ := P.geometry.edgePoint_surjective y
  rw [P.realizedHeatKernel_edge t ht e d u v]
  exact P.heatKernel_nonneg t ht e d u v

end TimeTraps.Analysis
