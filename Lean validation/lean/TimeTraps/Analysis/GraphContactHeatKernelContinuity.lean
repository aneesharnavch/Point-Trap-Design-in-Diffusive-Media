module

public import TimeTraps.Analysis.GraphContactHeatKernel
public import TimeTraps.Analysis.GraphContactHeatEvaluationContinuity

@[expose] public section

/-! Joint spatial continuity of the physical positive-time heat kernel.
Continuity of the Riesz vectors follows in L2 norm from the uniform H1
evaluation modulus; the kernel is their half-time inner product. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Analysis TimeTraps.Graph InnerProductSpace IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphContactOperatorProblem.heatKernel_continuous (P : GraphContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) :
    Continuous (fun z : Icc (0 : ℝ) (P.geometry.length e) × Icc (0 : ℝ) (P.geometry.length d) =>
      P.heatKernel t ht e z.1 d z.2) := by
  simp_rw [P.heatKernel_eq_inner]
  exact ((P.heatKernelVector_continuous (t / 2) (div_pos ht (by norm_num)) e).comp
    continuous_fst).inner
      ((P.heatKernelVector_continuous (t / 2) (div_pos ht (by norm_num)) d).comp continuous_snd)

end TimeTraps.Analysis
