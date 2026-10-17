module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section

/-! The inverse of an injective bounded operator as an actual partially
defined linear operator. Its domain is precisely the original range, and
its graph is closed in the ambient norm topology. Symmetry and injectivity
give a dense domain; no closed-range or bounded-inverse hypothesis is used. -/

namespace TimeTraps.Analysis

open Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def inverseOperator (T : E →L[ℝ] E) (hT : Function.Injective T) : E →ₗ.[ℝ] E where
  domain := T.range
  toFun := (LinearEquiv.ofInjective T.toLinearMap hT).symm.toLinearMap

theorem inverseOperator_domain (T : E →L[ℝ] E) (hT : Function.Injective T) :
    (inverseOperator T hT).domain = T.range := rfl

theorem inverseOperator_right_inverse (T : E →L[ℝ] E) (hT : Function.Injective T)
    (x : (inverseOperator T hT).domain) : T (inverseOperator T hT x) = x :=
  LinearEquiv.ofInjective_symm_apply T.toLinearMap x

theorem inverseOperator_apply_image (T : E →L[ℝ] E) (hT : Function.Injective T) (x : E) :
    inverseOperator T hT ⟨T x, LinearMap.mem_range_self T.toLinearMap x⟩ = x := by
  apply hT
  exact inverseOperator_right_inverse T hT _

theorem inverseOperator_graph_iff (T : E →L[ℝ] E) (hT : Function.Injective T) (x y : E) :
    (x, y) ∈ (inverseOperator T hT).graph ↔ T y = x := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨z, hz, hzy⟩
    change (z : E) = x at hz
    change inverseOperator T hT z = y at hzy
    rw [← hzy, inverseOperator_right_inverse T hT z, hz]
  · intro hxy
    refine ⟨⟨x, ⟨y, hxy⟩⟩, rfl, ?_⟩
    apply hT
    rw [inverseOperator_right_inverse T hT]
    exact hxy.symm

theorem inverseOperator_isClosed (T : E →L[ℝ] E) (hT : Function.Injective T) :
    (inverseOperator T hT).IsClosed := by
  have he : ((inverseOperator T hT).graph : Set (E × E)) = {p | T p.2 = p.1} := by
    ext p
    exact inverseOperator_graph_iff T hT p.1 p.2
  change IsClosed ((inverseOperator T hT).graph : Set (E × E))
  rw [he]
  exact isClosed_eq (T.continuous.comp continuous_snd) continuous_fst

theorem inverseOperator_isFormalAdjoint (T : E →L[ℝ] E) (hT : Function.Injective T)
    (hs : T.toLinearMap.IsSymmetric) :
    (inverseOperator T hT).IsFormalAdjoint (inverseOperator T hT) := by
  intro x y
  have h := hs (inverseOperator T hT x) (inverseOperator T hT y)
  change ⟪T (inverseOperator T hT x), inverseOperator T hT y⟫_ℝ =
    ⟪inverseOperator T hT x, T (inverseOperator T hT y)⟫_ℝ at h
  rw [inverseOperator_right_inverse T hT x, inverseOperator_right_inverse T hT y] at h
  exact h.symm

theorem inverseOperator_dense_domain [CompleteSpace E] (T : E →L[ℝ] E)
    (hT : Function.Injective T) (hs : T.toLinearMap.IsSymmetric) :
    Dense ((inverseOperator T hT).domain : Set E) := by
  have hk : T.rangeᗮ = ⊥ := hs.orthogonal_range.trans (LinearMap.ker_eq_bot.mpr hT)
  have hc : T.range.topologicalClosure = ⊤ := by
    rw [← T.range.orthogonal_orthogonal_eq_closure, hk, Submodule.bot_orthogonal_eq_top]
  rw [inverseOperator_domain, dense_iff_closure_eq]
  exact congrArg (fun S : Submodule ℝ E => (S : Set E)) hc

end TimeTraps.Analysis
