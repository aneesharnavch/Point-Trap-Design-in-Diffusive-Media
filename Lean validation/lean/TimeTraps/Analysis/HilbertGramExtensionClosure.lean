module

public import TimeTraps.Analysis.HilbertGramExtension

@[expose] public section

/-! The isometry determined by an equal-Gram family extends uniquely to
the actual topological closure of its algebraic span. Only the target
space needs completeness. -/

noncomputable section

namespace TimeTraps.Analysis

variable {I E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The algebraic span included isometrically in its topological closure. -/
def gramClosureInclusion (x : I → E) :
    Submodule.span ℝ (Set.range x) →ₗᵢ[ℝ]
      (Submodule.span ℝ (Set.range x)).topologicalClosure :=
  { Submodule.inclusion (Submodule.le_topologicalClosure _) with norm_map' := fun _ => rfl }

theorem gramClosureInclusion_dense (x : I → E) : DenseRange (gramClosureInclusion x) := by
  exact (denseRange_inclusion_iff (Submodule.le_topologicalClosure _)).mpr (fun _ h => h)

/-- The original generator as an element of the actual closed span. -/
def gramClosureGenerator (x : I → E) (i : I) :
    (Submodule.span ℝ (Set.range x)).topologicalClosure :=
  gramClosureInclusion x (gramSpanGenerator x i)

variable [CompleteSpace F]
variable (x : I → E) (y : I → F)
  (hGram : ∀ i j, inner ℝ (x i) (x j) = inner ℝ (y i) (y j))

/-- Continuous linear extension of the span isometry. -/
def gramClosureLinear : (Submodule.span ℝ (Set.range x)).topologicalClosure →L[ℝ] F :=
  (gramSpanIsometry x y hGram).toContinuousLinearMap.extend
    (gramClosureInclusion x).toContinuousLinearMap

theorem gramClosureLinear_span (v : Submodule.span ℝ (Set.range x)) :
    gramClosureLinear x y hGram (gramClosureInclusion x v) = gramSpanIsometry x y hGram v := by
  exact ContinuousLinearMap.extend_eq _ (gramClosureInclusion_dense x)
    (gramClosureInclusion x).isometry.isUniformInducing v

/-- The unique norm-preserving extension to the topological closed span. -/
def gramClosureIsometry : (Submodule.span ℝ (Set.range x)).topologicalClosure →ₗᵢ[ℝ] F :=
  { (gramClosureLinear x y hGram).toLinearMap with
    norm_map' := by
      intro z
      change ‖gramClosureLinear x y hGram z‖ = ‖z‖
      refine (gramClosureInclusion_dense x).induction_on z
        (isClosed_eq (gramClosureLinear x y hGram).continuous.norm continuous_norm) ?_
      intro v
      rw [gramClosureLinear_span]
      exact (gramSpanIsometry x y hGram).norm_map v }

/-- The closed-span extension agrees with the algebraic-span map. -/
theorem gramClosureIsometry_span (v : Submodule.span ℝ (Set.range x)) :
    gramClosureIsometry x y hGram (gramClosureInclusion x v) = gramSpanIsometry x y hGram v :=
  gramClosureLinear_span x y hGram v

/-- Every original generator has its prescribed image after completion. -/
theorem gramClosureIsometry_generator (i : I) :
    gramClosureIsometry x y hGram (gramClosureGenerator x i) = y i := by
  rw [gramClosureGenerator, gramClosureIsometry_span, gramSpanIsometry_generator]

/-- Agreement on the generators determines every continuous linear map
on the closed span, even without an isometry hypothesis on that map. -/
theorem gramClosureIsometry_unique
    (f : (Submodule.span ℝ (Set.range x)).topologicalClosure →L[ℝ] F)
    (hf : ∀ i, f (gramClosureGenerator x i) = y i) :
    f = (gramClosureIsometry x y hGram).toContinuousLinearMap := by
  have hs := gramSpanIsometry_unique x y hGram
    (f.toLinearMap.comp (gramClosureInclusion x).toLinearMap) hf
  apply ContinuousLinearMap.ext
  intro z
  change f z = gramClosureIsometry x y hGram z
  refine (gramClosureInclusion_dense x).induction_on z
    (isClosed_eq f.continuous (gramClosureIsometry x y hGram).continuous) ?_
  intro v
  rw [gramClosureIsometry_span]
  exact LinearMap.congr_fun hs v

end TimeTraps.Analysis

end
