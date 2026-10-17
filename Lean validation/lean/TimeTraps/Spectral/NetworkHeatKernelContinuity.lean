module

public import TimeTraps.Spectral.NetworkHeatKernel
public import TimeTraps.Analysis.IntervalSobolevEvaluationContinuity

@[expose] public section

/-! Joint spatial continuity of the physical positive-time heat kernel.
Continuity of the Riesz vectors follows in L2 norm from the uniform H1
evaluation modulus; the kernel is their half-time inner product. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Graph InnerProductSpace IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance intervalKernelNormedSpace (l r : ℝ) :
    NormedSpace ℝ (IntervalSobolevSpace l r) := Submodule.normedSpace (intervalSobolevGraph l r)

noncomputable local instance graphKernelNormedSpace (G : MetricGraph V E) :
    NormedSpace ℝ (GraphSobolevSpace G) := Submodule.normedSpace (graphSobolevSubspace G)

theorem SpectralNetwork.heatPointEvaluation_continuous (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    Continuous (fun x : Icc (0 : ℝ) (P.length e) => P.heatPointEvaluation t ht e x) :=
  ((evalL_continuous (P.length_pos e)).clm_comp_const (P.operatorEdgeL e)).clm_comp_const
    (P.heatSobolevL t ht)

theorem SpectralNetwork.heatKernelVector_continuous (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    Continuous (fun x : Icc (0 : ℝ) (P.length e) => P.heatKernelVector t ht e x) :=
  (toDual ℝ (GraphL2Product P.geometry)).symm.continuous.comp
    (P.heatPointEvaluation_continuous t ht e)

theorem SpectralNetwork.heatKernel_continuous (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) :
    Continuous (fun z : Icc (0 : ℝ) (P.length e) × Icc (0 : ℝ) (P.length d) =>
      P.heatKernel t ht e z.1 d z.2) := by
  simp_rw [P.heatKernel_eq_inner]
  exact ((P.heatKernelVector_continuous (t / 2) (div_pos ht (by norm_num)) e).comp
    continuous_fst).inner
      ((P.heatKernelVector_continuous (t / 2) (div_pos ht (by norm_num)) d).comp continuous_snd)

end TimeTraps.Spectral
