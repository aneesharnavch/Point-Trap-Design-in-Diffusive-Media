module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear isometries from equal Gram families

Equal pairwise inner products determine an isometry of the algebraic spans.
The construction descends finite linear combinations, so it does not require
the generating family to be linearly independent.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace TimeTraps.Analysis

variable {I E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable (x : I → E) (y : I → F)
  (hGram : ∀ i j, inner ℝ (x i) (x j) = inner ℝ (y i) (y j))

include hGram in
/-- Every finite combination has the same norm for equal-Gram families. -/
theorem gram_linearCombination_norm (c : I →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ y c‖ = ‖Finsupp.linearCombination ℝ x c‖ := by
  have hi : inner ℝ (Finsupp.linearCombination ℝ x c)
      (Finsupp.linearCombination ℝ x c) =
      inner ℝ (Finsupp.linearCombination ℝ y c) (Finsupp.linearCombination ℝ y c) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
      real_inner_smul_left, real_inner_smul_right, hGram]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (Finsupp.linearCombination ℝ x c),
    norm_nonneg (Finsupp.linearCombination ℝ y c)]

/-- The original generator, regarded as a vector in its algebraic span. -/
def gramSpanGenerator (i : I) : Submodule.span ℝ (Set.range x) :=
  ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩

/-- A finite combination regarded as a vector in the algebraic span. -/
def gramSpanCombination (c : I →₀ ℝ) : Submodule.span ℝ (Set.range x) :=
  ⟨Finsupp.linearCombination ℝ x c, by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ c⟩

/-- Descend the map on finite combinations to their actual span. -/
def gramSpanLinear : Submodule.span ℝ (Set.range x) →ₗ[ℝ] F :=
  (Finsupp.linearCombination ℝ y).compLeftInverse (Finsupp.linearCombination ℝ x) |>.toLinearMap
    |>.comp (Submodule.inclusion (by rw [Finsupp.range_linearCombination]))

include hGram in
theorem gramSpanLinear_combination (c : I →₀ ℝ) :
    gramSpanLinear x y (gramSpanCombination x c) = Finsupp.linearCombination ℝ y c := by
  exact LinearMap.compLeftInverse_apply_of_bdd _ _
    ⟨1, fun c => by simpa using (gram_linearCombination_norm x y hGram c).le⟩ _ _ rfl

/-- The norm-preserving linear map determined by an equal-Gram family. -/
def gramSpanIsometry : Submodule.span ℝ (Set.range x) →ₗᵢ[ℝ] F :=
  { gramSpanLinear x y with
    norm_map' := by
      intro z
      obtain ⟨c, hc⟩ := (show (z : E) ∈ (Finsupp.linearCombination ℝ x).range by
        rw [Finsupp.range_linearCombination]
        exact z.property)
      have hz : z = gramSpanCombination x c := Subtype.ext hc.symm
      rw [hz, gramSpanLinear_combination x y hGram]
      exact gram_linearCombination_norm x y hGram c }

/-- The isometry agrees with the prescribed image of every generator. -/
theorem gramSpanIsometry_generator (i : I) :
    gramSpanIsometry x y hGram (gramSpanGenerator x i) = y i := by
  have hz : gramSpanGenerator x i = gramSpanCombination x (Finsupp.single i 1) := by
    apply Subtype.ext
    simp [gramSpanGenerator, gramSpanCombination]
  change gramSpanLinear x y (gramSpanGenerator x i) = y i
  rw [hz, gramSpanLinear_combination x y hGram]
  simp

/-- Agreement on the original family determines any linear map on the span. -/
theorem gramSpanIsometry_unique (f : Submodule.span ℝ (Set.range x) →ₗ[ℝ] F)
    (hf : ∀ i, f (gramSpanGenerator x i) = y i) :
    f = (gramSpanIsometry x y hGram).toLinearMap := by
  apply LinearMap.ext
  intro z
  have h : ∀ v hv, f ⟨v, hv⟩ = gramSpanIsometry x y hGram ⟨v, hv⟩ := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      exact (hf i).trans (gramSpanIsometry_generator x y hGram i).symm
    | zero => exact (map_zero f).trans (map_zero (gramSpanIsometry x y hGram)).symm
    | add v w hv hw ihv ihw =>
      change f (⟨v, hv⟩ + ⟨w, hw⟩) = gramSpanIsometry x y hGram (⟨v, hv⟩ + ⟨w, hw⟩)
      rw [map_add, map_add, ihv, ihw]
    | smul a v hv ih =>
      change f (a • ⟨v, hv⟩) = gramSpanIsometry x y hGram (a • ⟨v, hv⟩)
      rw [map_smul, map_smul, ih]
  exact h z z.property

end TimeTraps.Analysis

end
