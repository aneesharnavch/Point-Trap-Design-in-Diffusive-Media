module

public import TimeTraps.Analysis.InverseOperator

@[expose] public section

/-! Self-adjointness of the densely defined inverse, using Mathlib's
actual unbounded adjoint. An adjoint graph pair (z,w) satisfies
<f,z> = <T f,w> for every f. Symmetry then forces z=T w, proving exact
equality of both the graph and domain, rather than only formal symmetry. -/

namespace TimeTraps.Analysis

open Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem inverseOperator_adjoint_graph_iff (T : E →L[ℝ] E) (hT : Function.Injective T)
    (hs : T.toLinearMap.IsSymmetric) (z w : E) :
    (z, w) ∈ (inverseOperator T hT).adjoint.graph ↔ T w = z := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (inverseOperator_dense_domain T hT hs),
    Submodule.mem_adjoint_iff]
  constructor
  · intro h
    have he : ∀ f : E, ⟪f, z⟫_ℝ = ⟪f, T w⟫_ℝ := by
      intro f
      have hf := h (T f) f ((inverseOperator_graph_iff T hT (T f) f).mpr rfl)
      change ⟪f, z⟫_ℝ - ⟪T f, w⟫_ℝ = 0 at hf
      have hsym : ⟪T f, w⟫_ℝ = ⟪f, T w⟫_ℝ := hs f w
      rw [hsym] at hf
      exact sub_eq_zero.mp hf
    exact (ext_inner_left ℝ he).symm
  · intro hw a b hab
    have hba := (inverseOperator_graph_iff T hT a b).mp hab
    change ⟪b, z⟫_ℝ - ⟪a, w⟫_ℝ = 0
    rw [← hw, ← hba]
    have hsym : ⟪T b, w⟫_ℝ = ⟪b, T w⟫_ℝ := hs b w
    rw [hsym, sub_self]

theorem inverseOperator_adjoint_eq (T : E →L[ℝ] E) (hT : Function.Injective T)
    (hs : T.toLinearMap.IsSymmetric) :
    (inverseOperator T hT).adjoint = inverseOperator T hT := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [inverseOperator_adjoint_graph_iff T hT hs p.1 p.2,
    inverseOperator_graph_iff T hT p.1 p.2]

theorem inverseOperator_adjoint_domain (T : E →L[ℝ] E) (hT : Function.Injective T)
    (hs : T.toLinearMap.IsSymmetric) :
    (inverseOperator T hT).adjoint.domain = T.range := by
  rw [inverseOperator_adjoint_eq T hT hs, inverseOperator_domain]

theorem inverseOperator_isSelfAdjoint (T : E →L[ℝ] E) (hT : Function.Injective T)
    (hs : T.toLinearMap.IsSymmetric) : IsSelfAdjoint (inverseOperator T hT) :=
  LinearPMap.isSelfAdjoint_def.mpr (inverseOperator_adjoint_eq T hT hs)

end TimeTraps.Analysis
