module

public import TimeTraps.Analysis.ShiftedInverseOperator

@[expose] public section

/-! Exact self-adjointness of the translated inverse R⁻¹-cI. The proof
identifies the actual adjoint graph using the dense inverse domain and
symmetry of R; no positivity of R⁻¹-cI is required. -/

namespace TimeTraps.Analysis

open Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem translatedInverseOperator_adjoint_graph_iff (T : E →L[ℝ] E)
    (hT : Function.Injective T) (hs : T.toLinearMap.IsSymmetric) (c : ℝ) (z w : E) :
    (z, w) ∈ (translatedInverseOperator T hT c).adjoint.graph ↔ T (w + c • z) = z := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (translatedInverseOperator_dense_domain T hT hs c),
    Submodule.mem_adjoint_iff]
  constructor
  · intro h
    have he : ∀ f : E, ⟪f, z⟫_ℝ = ⟪f, T (w + c • z)⟫_ℝ := by
      intro f
      have hg : (T f, f - c • T f) ∈ (translatedInverseOperator T hT c).graph :=
        (translatedInverseOperator_graph_iff T hT c _ _).mpr (by rw [sub_add_cancel])
      have hf := h (T f) (f - c • T f) hg
      change ⟪f - c • T f, z⟫_ℝ - ⟪T f, w⟫_ℝ = 0 at hf
      rw [inner_sub_left, real_inner_smul_left] at hf
      have hsym : ⟪T f, w + c • z⟫_ℝ = ⟪f, T (w + c • z)⟫_ℝ := hs f _
      rw [← hsym, inner_add_right, inner_smul_right]
      linarith
    exact (ext_inner_left ℝ he).symm
  · intro hw a b hab
    have hba := (translatedInverseOperator_graph_iff T hT c a b).mp hab
    change ⟪b, z⟫_ℝ - ⟪a, w⟫_ℝ = 0
    have he : ⟪b + c • a, z⟫_ℝ = ⟪a, w + c • z⟫_ℝ := by
      calc
        _ = ⟪b + c • a, T (w + c • z)⟫_ℝ := congrArg (fun q => ⟪b + c • a, q⟫_ℝ) hw.symm
        _ = ⟪T (b + c • a), w + c • z⟫_ℝ := (hs _ _).symm
        _ = _ := by rw [hba]
    rw [inner_add_left, real_inner_smul_left, inner_add_right, inner_smul_right] at he
    linarith

theorem translatedInverseOperator_adjoint_eq (T : E →L[ℝ] E)
    (hT : Function.Injective T) (hs : T.toLinearMap.IsSymmetric) (c : ℝ) :
    (translatedInverseOperator T hT c).adjoint = translatedInverseOperator T hT c := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [translatedInverseOperator_adjoint_graph_iff T hT hs c p.1 p.2,
    translatedInverseOperator_graph_iff T hT c p.1 p.2]

theorem translatedInverseOperator_adjoint_domain (T : E →L[ℝ] E)
    (hT : Function.Injective T) (hs : T.toLinearMap.IsSymmetric) (c : ℝ) :
    (translatedInverseOperator T hT c).adjoint.domain = T.range := by
  rw [translatedInverseOperator_adjoint_eq T hT hs c, translatedInverseOperator_domain]

theorem translatedInverseOperator_isSelfAdjoint (T : E →L[ℝ] E)
    (hT : Function.Injective T) (hs : T.toLinearMap.IsSymmetric) (c : ℝ) :
    IsSelfAdjoint (translatedInverseOperator T hT c) :=
  LinearPMap.isSelfAdjoint_def.mpr (translatedInverseOperator_adjoint_eq T hT hs c)

end TimeTraps.Analysis
