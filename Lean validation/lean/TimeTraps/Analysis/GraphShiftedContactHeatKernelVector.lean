module

public import TimeTraps.Analysis.GraphShiftedContactHeatPointOrder
public import TimeTraps.Analysis.CompactHeatSymmetry
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

/-! Riesz vectors of actual positive-time network point evaluation. Their
heat evolution follows from the physical H1 semigroup identity and symmetry;
their definition does not select point values of arbitrary L2 functions. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.heatKernelVector (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    GraphL2Product P.geometry :=
  (toDual ℝ (GraphL2Product P.geometry)).symm (P.heatPointEvaluation t ht e x)

theorem GraphShiftedContactOperatorProblem.heatKernelVector_inner (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (f : GraphL2Product P.geometry) :
    inner ℝ (P.heatKernelVector t ht e x) f = P.heatPointEvaluation t ht e x f :=
  toDual_symm_apply

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_add (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (f : GraphL2Product P.geometry) :
    P.heatPointEvaluation (s + t) (lt_add_of_lt_of_nonneg hs (show 0 ≤ t from zero_le)) e x f =
      P.heatPointEvaluation s hs e x (P.heatSemigroup t f) := by
  rw [P.heatPointEvaluation_apply, P.heatPointEvaluation_apply, P.heatSobolevL_add]

theorem GraphShiftedContactOperatorProblem.heatKernelVector_add (P : GraphShiftedContactOperatorProblem V E)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    P.heatKernelVector (s + t) (lt_add_of_lt_of_nonneg hs (show 0 ≤ t from zero_le)) e x =
      P.heatSemigroup t (P.heatKernelVector s hs e x) := by
  apply ext_inner_right ℝ
  intro f
  calc
    _ = P.heatPointEvaluation (s + t) _ e x f := P.heatKernelVector_inner _ _ e x f
    _ = P.heatPointEvaluation s hs e x (P.heatSemigroup t f) :=
      P.heatPointEvaluation_add s hs t e x f
    _ = inner ℝ (P.heatKernelVector s hs e x) (P.heatSemigroup t f) :=
      (P.heatKernelVector_inner s hs e x (P.heatSemigroup t f)).symm
    _ = _ := (P.heatSemigroup_symmetric t _ _).symm

theorem GraphShiftedContactOperatorProblem.heatKernelVector_positive_pairing (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (f : GraphL2Product P.geometry)
    (hf : ∀ d, ∀ᵐ y ∂volume.restrict (Ioo 0 (P.geometry.length d)), 0 ≤ (f d) y) :
    0 ≤ inner ℝ (P.heatKernelVector t ht e x) f := by
  rw [P.heatKernelVector_inner]
  exact P.heatPointEvaluation_nonneg t ht f hf e x

theorem GraphShiftedContactOperatorProblem.heatKernelVector_tail (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    P.heatKernelVector t ht e ⟨0, le_rfl, (P.geometry.length_pos e).le⟩ =
      (toDual ℝ (GraphL2Product P.geometry)).symm (P.heatNodeEvaluation t ht (P.geometry.tail e)) := by
  unfold heatKernelVector
  rw [P.heatPointEvaluation_tail]

theorem GraphShiftedContactOperatorProblem.heatKernelVector_head (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    P.heatKernelVector t ht e ⟨P.geometry.length e, (P.geometry.length_pos e).le, le_rfl⟩ =
      (toDual ℝ (GraphL2Product P.geometry)).symm (P.heatNodeEvaluation t ht (P.geometry.head e)) := by
  unfold heatKernelVector
  rw [P.heatPointEvaluation_head]

end TimeTraps.Analysis
