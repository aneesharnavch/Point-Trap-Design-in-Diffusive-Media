module

public import TimeTraps.Analysis.InverseOperator

@[expose] public section

/-! Subtract a real scalar multiple of the identity from the actual
unbounded inverse. Its domain is unchanged and its graph is characterized
without assuming positivity or invertibility of the translated operator. -/

namespace TimeTraps.Analysis

open Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def translatedInverseOperator (T : E →L[ℝ] E)
    (hT : Function.Injective T) (c : ℝ) : E →ₗ.[ℝ] E where
  domain := T.range
  toFun := (show T.range →ₗ[ℝ] E from (inverseOperator T hT).toFun) - c • T.range.subtype

theorem translatedInverseOperator_domain (T : E →L[ℝ] E)
    (hT : Function.Injective T) (c : ℝ) :
    (translatedInverseOperator T hT c).domain = T.range := rfl

theorem translatedInverseOperator_apply (T : E →L[ℝ] E)
    (hT : Function.Injective T) (c : ℝ) (u : (translatedInverseOperator T hT c).domain) :
    translatedInverseOperator T hT c u = inverseOperator T hT u - c • (u : E) := rfl

theorem translatedInverseOperator_graph_iff (T : E →L[ℝ] E)
    (hT : Function.Injective T) (c : ℝ) (x y : E) :
    (x, y) ∈ (translatedInverseOperator T hT c).graph ↔ T (y + c • x) = x := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u, hu, huy⟩
    change (u : E) = x at hu
    change inverseOperator T hT u - c • (u : E) = y at huy
    calc
      T (y + c • x) = T (inverseOperator T hT u) := by rw [← huy, ← hu, sub_add_cancel]
      _ = (u : E) := inverseOperator_right_inverse T hT u
      _ = x := hu
  · intro h
    let u : (translatedInverseOperator T hT c).domain := ⟨x, ⟨y + c • x, h⟩⟩
    have hu : inverseOperator T hT u = y + c • x := by
      apply hT
      exact (inverseOperator_right_inverse T hT u).trans h.symm
    refine ⟨u, rfl, ?_⟩
    change inverseOperator T hT u - c • x = y
    rw [hu, add_sub_cancel_right]

theorem translatedInverseOperator_isClosed (T : E →L[ℝ] E)
    (hT : Function.Injective T) (c : ℝ) : (translatedInverseOperator T hT c).IsClosed := by
  have he : ((translatedInverseOperator T hT c).graph : Set (E × E)) =
      {p | T (p.2 + c • p.1) = p.1} := by
    ext p
    exact translatedInverseOperator_graph_iff T hT c p.1 p.2
  change IsClosed ((translatedInverseOperator T hT c).graph : Set (E × E))
  rw [he]
  exact isClosed_eq (T.continuous.comp
    (continuous_snd.add (continuous_const.smul continuous_fst))) continuous_fst

theorem translatedInverseOperator_dense_domain [CompleteSpace E] (T : E →L[ℝ] E)
    (hT : Function.Injective T) (hs : T.toLinearMap.IsSymmetric) (c : ℝ) :
    Dense ((translatedInverseOperator T hT c).domain : Set E) :=
  inverseOperator_dense_domain T hT hs

end TimeTraps.Analysis
