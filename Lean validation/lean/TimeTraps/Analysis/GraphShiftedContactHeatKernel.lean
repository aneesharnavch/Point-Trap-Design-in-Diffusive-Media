module

public import TimeTraps.Analysis.GraphShiftedContactHeatKernelVector
public import TimeTraps.Analysis.GraphL2PositiveDual

@[expose] public section

/-! A physical continuous representative of the graph heat kernel,
constructed from the Riesz vector at half-time and the actual H1 heat map.
Its nonnegativity follows from self-duality of the original L2 cone. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.heatKernelVector_nonneg_ae (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    ∀ d, ∀ᵐ y ∂volume.restrict (Ioo 0 (P.geometry.length d)), 0 ≤ (P.heatKernelVector t ht e x d) y :=
  graphL2_nonneg_of_positive_pairing P.geometry (P.heatKernelVector t ht e x)
    (P.heatKernelVector_positive_pairing t ht e x)

noncomputable def GraphShiftedContactOperatorProblem.heatKernel (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) : E → ℝ → ℝ :=
  P.operatorRep (P.heatSobolevL (t / 2) (div_pos ht (by norm_num))
    (P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) e x))

theorem GraphShiftedContactOperatorProblem.heatKernel_eq_inner (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E)
    (x : Icc (0 : ℝ) (P.geometry.length e)) (y : Icc (0 : ℝ) (P.geometry.length d)) :
    P.heatKernel t ht e x d y =
      inner ℝ (P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) e x)
        (P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) d y) := by
  change P.heatPointEvaluation (t / 2) _ d y (P.heatKernelVector (t / 2) _ e x) = _
  exact (P.heatKernelVector_inner (t / 2) _ d y _).symm.trans (real_inner_comm _ _)

theorem GraphShiftedContactOperatorProblem.heatKernel_symmetric (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E)
    (x : Icc (0 : ℝ) (P.geometry.length e)) (y : Icc (0 : ℝ) (P.geometry.length d)) :
    P.heatKernel t ht e x d y = P.heatKernel t ht d y e x := by
  rw [P.heatKernel_eq_inner, P.heatKernel_eq_inner]
  exact real_inner_comm _ _

theorem GraphShiftedContactOperatorProblem.heatKernel_nonneg (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E)
    (x : Icc (0 : ℝ) (P.geometry.length e)) (y : Icc (0 : ℝ) (P.geometry.length d)) :
    0 ≤ P.heatKernel t ht e x d y :=
  P.heatPointEvaluation_nonneg (t / 2) (div_pos ht (by norm_num))
    (P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) e x)
    (P.heatKernelVector_nonneg_ae (t / 2) (div_pos ht (by norm_num)) e x) d y

theorem GraphShiftedContactOperatorProblem.heatKernel_energy (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    ∃ U : V → ℝ, GraphEnergy P.geometry U (P.heatKernel t ht e x) :=
  ⟨_, P.operatorRep_energy _⟩

theorem GraphShiftedContactOperatorProblem.heatKernel_representative (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) (d : E) :
    (P.heatKernelVector t ht e x) d =ᵐ[volume.restrict (Ioo 0 (P.geometry.length d))]
      P.heatKernel t ht e x d := by
  have he : P.heatKernelVector t ht e x =
      P.heatSemigroup (t / 2) (P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) e x) := by
    have h := P.heatKernelVector_add (t / 2) (div_pos ht (by norm_num)) (t / 2) e x
    simpa only [add_halves] using h
  rw [he]
  exact P.heatSobolevL_state_ae (t / 2) (div_pos ht (by norm_num)) _ d

end TimeTraps.Analysis
