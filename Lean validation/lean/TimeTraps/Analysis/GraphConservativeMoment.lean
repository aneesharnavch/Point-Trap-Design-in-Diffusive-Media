module

public import TimeTraps.Analysis.GraphConservativeMomentEstimate

@[expose] public section

/-! Literal transition moments of scalar graph coordinates. The original
operator-domain identities and generator bounds are explicit inputs;
the resulting second and fourth moments are genuine kernel integrals. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def graphConservativeCenteredPower (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (x : GraphRealization G) (n : ℕ) : C(GraphRealization G, ℝ) :=
  (f - ContinuousMap.const _ (f x)) ^ n

omit [Fintype V] [Fintype E] [Nonempty E] in
theorem graphConservativeCenteredPower_apply (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) (x y : GraphRealization G) (n : ℕ) :
    graphConservativeCenteredPower G f x n y = (f y - f x) ^ n := rfl

theorem GraphShiftedContactOperatorProblem.realizedTransition_coordinate_moment_integrable
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (x : GraphRealization P.geometry) (n : ℕ) (T : ℝ≥0) :
    Integrable (fun y => (f y - f x) ^ n) (P.realizedTransition T x) :=
  P.realizedFeller_integrable T (graphConservativeCenteredPower P.geometry f x n) x

theorem GraphShiftedContactOperatorProblem.realizedTransition_coordinate_moments
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (f : C(GraphRealization P.geometry, ℝ))
    (g₂ g₄ : GraphRealization P.geometry → C(GraphRealization P.geometry, ℝ))
    (h₂ : ∀ x, (graphConservativeContinuousStateL P.geometry (graphConservativeCenteredPower P.geometry f x 2),
      -graphConservativeContinuousStateL P.geometry (g₂ x)) ∈ P.operator.graph)
    (h₄ : ∀ x, (graphConservativeContinuousStateL P.geometry (graphConservativeCenteredPower P.geometry f x 4),
      -graphConservativeContinuousStateL P.geometry (g₄ x)) ∈ P.operator.graph)
    {C₂ C₄ : ℝ} (hC₄ : 0 ≤ C₄) (hg₂ : ∀ x z, g₂ x z ≤ C₂)
    (hg₄ : ∀ x z, g₄ x z ≤ C₄ * (f z - f x) ^ 2)
    (T : ℝ≥0) (x : GraphRealization P.geometry) :
    (∫ y, (f y - f x) ^ 2 ∂P.realizedTransition T x) ≤ C₂ * T.val ∧
      (∫ y, (f y - f x) ^ 4 ∂P.realizedTransition T x) ≤ C₂ * C₄ * T.val ^ 2 / 2 := by
  have hx₂ : graphConservativeCenteredPower P.geometry f x 2 x = 0 := by
    simp only [graphConservativeCenteredPower_apply, sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  have hx₄ : graphConservativeCenteredPower P.geometry f x 4 x = 0 := by
    simp only [graphConservativeCenteredPower_apply, sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  have hs := P.realizedFeller_generator_bound hκ
    (graphConservativeCenteredPower P.geometry f x 2) (g₂ x) (h₂ x) (hg₂ x) x hx₂ T
  have hf := P.realizedFeller_generator_quadratic_bound hκ
    (graphConservativeCenteredPower P.geometry f x 2) (graphConservativeCenteredPower P.geometry f x 4)
    (g₂ x) (g₄ x) (h₂ x) (h₄ x) hC₄ (hg₂ x) (hg₄ x) x hx₂ hx₄ T
  rw [P.realizedFeller_apply] at hs hf
  exact ⟨hs, hf⟩

end TimeTraps.Analysis
