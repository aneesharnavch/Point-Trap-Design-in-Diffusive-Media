module

public import TimeTraps.Analysis.GraphConservativeCoordinateComposition

@[expose] public section

/-! The literal centered square and fourth power of every separating
coordinate are in the true conservative operator domain. Their exact
generators supply the second-to-fourth moment argument for continuous paths. -/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.coordinateCentered (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (c : ℝ) : C(GraphRealization G, ℝ) :=
  G.coordinateTest φ - ContinuousMap.const _ c

noncomputable def MetricGraph.coordinateSquareGenerator (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (c : ℝ) : C(GraphRealization G, ℝ) :=
  (2 : ℝ) • (G.coordinateCentered φ c * G.coordinateGenerator φ) +
    (2 : ℝ) • G.coordinateEnergyDensity φ

noncomputable def MetricGraph.coordinateFourthGenerator (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (c : ℝ) : C(GraphRealization G, ℝ) :=
  (4 : ℝ) • (G.coordinateCentered φ c ^ 3 * G.coordinateGenerator φ) +
    (12 : ℝ) • (G.coordinateCentered φ c ^ 2 * G.coordinateEnergyDensity φ)

end TimeTraps.Graph

namespace TimeTraps.Analysis

open TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.coordinate_square_operator_graph
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (c : ℝ) :
    (graphConservativeContinuousStateL P.geometry (P.geometry.coordinateCentered φ c ^ 2),
      graphConservativeContinuousStateL P.geometry (-P.geometry.coordinateSquareGenerator φ c))
        ∈ P.operator.graph := by
  let F : C(ℝ, ℝ) := ⟨fun z => (z - c) ^ 2, by fun_prop⟩
  let F₁ : C(ℝ, ℝ) := ⟨fun z => 2 * (z - c), by fun_prop⟩
  let F₂ : C(ℝ, ℝ) := ContinuousMap.const _ 2
  have hF : ∀ z, HasDerivAt F (F₁ z) z := by
    intro z
    change HasDerivAt (fun y => (y - c) ^ 2) (2 * (z - c)) z
    convert! ((hasDerivAt_id z).sub_const c).pow 2 using 1
    norm_num
  have hF₁ : ∀ z, HasDerivAt F₁ (F₂ z) z := by
    intro z
    change HasDerivAt (fun y => 2 * (y - c)) 2 z
    convert! ((hasDerivAt_id z).sub_const c).const_mul 2 using 1
    norm_num
  have he₀ : F.comp (P.geometry.coordinateTest φ) = P.geometry.coordinateCentered φ c ^ 2 := by
    ext p
    rfl
  have he₁ : (F₁.comp (P.geometry.coordinateTest φ)) * P.geometry.coordinateGenerator φ +
      (F₂.comp (P.geometry.coordinateTest φ)) * P.geometry.coordinateEnergyDensity φ =
      P.geometry.coordinateSquareGenerator φ c := by
    ext p
    change 2 * (P.geometry.coordinateTest φ p - c) * P.geometry.coordinateGenerator φ p +
      2 * P.geometry.coordinateEnergyDensity φ p =
      2 * ((P.geometry.coordinateTest φ p - c) * P.geometry.coordinateGenerator φ p) +
      2 * P.geometry.coordinateEnergyDensity φ p
    ring
  simpa only [he₀, he₁] using P.coordinate_composition_operator_graph hκ φ F F₁ F₂ hF hF₁

theorem GraphShiftedContactOperatorProblem.coordinate_fourth_operator_graph
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (c : ℝ) :
    (graphConservativeContinuousStateL P.geometry (P.geometry.coordinateCentered φ c ^ 4),
      graphConservativeContinuousStateL P.geometry (-P.geometry.coordinateFourthGenerator φ c))
        ∈ P.operator.graph := by
  let F : C(ℝ, ℝ) := ⟨fun z => (z - c) ^ 4, by fun_prop⟩
  let F₁ : C(ℝ, ℝ) := ⟨fun z => 4 * (z - c) ^ 3, by fun_prop⟩
  let F₂ : C(ℝ, ℝ) := ⟨fun z => 12 * (z - c) ^ 2, by fun_prop⟩
  have hF : ∀ z, HasDerivAt F (F₁ z) z := by
    intro z
    change HasDerivAt (fun y => (y - c) ^ 4) (4 * (z - c) ^ 3) z
    convert! ((hasDerivAt_id z).sub_const c).pow 4 using 1
    norm_num
  have hF₁ : ∀ z, HasDerivAt F₁ (F₂ z) z := by
    intro z
    change HasDerivAt (fun y => 4 * (y - c) ^ 3) (12 * (z - c) ^ 2) z
    convert! (((hasDerivAt_id z).sub_const c).pow 3).const_mul 4 using 1
    norm_num
    ring
  have he₀ : F.comp (P.geometry.coordinateTest φ) = P.geometry.coordinateCentered φ c ^ 4 := by
    ext p
    rfl
  have he₁ : (F₁.comp (P.geometry.coordinateTest φ)) * P.geometry.coordinateGenerator φ +
      (F₂.comp (P.geometry.coordinateTest φ)) * P.geometry.coordinateEnergyDensity φ =
      P.geometry.coordinateFourthGenerator φ c := by
    ext p
    change 4 * (P.geometry.coordinateTest φ p - c) ^ 3 * P.geometry.coordinateGenerator φ p +
      (12 * (P.geometry.coordinateTest φ p - c) ^ 2) * P.geometry.coordinateEnergyDensity φ p =
      4 * ((P.geometry.coordinateTest φ p - c) ^ 3 * P.geometry.coordinateGenerator φ p) +
      12 * ((P.geometry.coordinateTest φ p - c) ^ 2 * P.geometry.coordinateEnergyDensity φ p)
    ring
  simpa only [he₀, he₁] using P.coordinate_composition_operator_graph hκ φ F F₁ F₂ hF hF₁

end TimeTraps.Analysis
