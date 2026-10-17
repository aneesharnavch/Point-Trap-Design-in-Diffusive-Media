module

public import TimeTraps.Analysis.GraphConservativeCoordinateOperator
public import TimeTraps.Analysis.GraphConservativeCoordinateEnergy

@[expose] public section

/-! Twice continuously differentiable scalar compositions of the actual
separating coordinates remain in the original conservative graph domain.
The chain rule retains the original variable conductance through J^2/a. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

theorem EdgeEquation.comp_twice {a u j h : ℝ → ℝ} {l r : ℝ}
    (heq : EdgeEquation a (fun x => -h x) l r u j)
    (F F₁ F₂ : C(ℝ, ℝ))
    (hF : ∀ z, HasDerivAt F (F₁ z) z) (hF₁ : ∀ z, HasDerivAt F₁ (F₂ z) z) :
    EdgeEquation a (fun x => -(F₁ (u x) * h x + F₂ (u x) * (j x ^ 2 / a x))) l r
      (fun x => F (u x)) (fun x => F₁ (u x) * j x) := by
  refine ⟨F.continuous.comp_continuousOn heq.state_continuous,
    (F₁.continuous.comp_continuousOn heq.state_continuous).mul heq.flux_continuous, ?_, ?_⟩
  · intro x hx
    convert! (hF (u x)).comp x (heq.state_derivative x hx) using 1
    ring
  · intro x hx
    have hd : HasDerivAt j (h x) x := by
      simpa only [neg_neg] using heq.flux_derivative x hx
    convert! ((hF₁ (u x)).comp x (heq.state_derivative x hx)).mul hd using 1
    dsimp
    ring

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.coordinate_composition_operator_graph
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (F F₁ F₂ : C(ℝ, ℝ))
    (hF : ∀ z, HasDerivAt F (F₁ z) z) (hF₁ : ∀ z, HasDerivAt F₁ (F₂ z) z) :
    (graphConservativeContinuousStateL P.geometry (F.comp (P.geometry.coordinateTest φ)),
      graphConservativeContinuousStateL P.geometry
        (-((F₁.comp (P.geometry.coordinateTest φ)) * P.geometry.coordinateGenerator φ +
          (F₂.comp (P.geometry.coordinateTest φ)) * P.geometry.coordinateEnergyDensity φ)))
            ∈ P.operator.graph := by
  let u := P.geometry.coordinateEdgeValue φ
  let j := P.geometry.coordinateEdgeFlux φ
  let h := P.geometry.coordinateEdgeGenerator φ
  let k : E → ℝ → ℝ := fun e x => F₁ (u e x) * h e x +
    F₂ (u e x) * (j e x ^ 2 / P.geometry.conductance e x)
  have heq : ∀ e, EdgeEquation (P.geometry.conductance e) (fun x => -k e x)
      0 (P.geometry.length e) (fun x => F (u e x)) (fun x => F₁ (u e x) * j e x) :=
    fun e => (P.geometry.coordinateEdge_equation φ e).comp_twice F F₁ F₂ hF hF₁
  have hk : ∀ e, ContinuousOn (k e) (Icc 0 (P.geometry.length e)) := by
    intro e
    exact ((F₁.continuous.comp_continuousOn (P.geometry.coordinateEdgeValue_continuous φ e)).mul
      (P.geometry.coordinateEdgeGenerator_continuous φ e)).add
      ((F₂.continuous.comp_continuousOn (P.geometry.coordinateEdgeValue_continuous φ e)).mul
        (P.geometry.coordinateEdgeEnergyDensity_continuous φ e))
  have hu : GraphEnergy P.geometry (fun v => F (φ (graphVertexCoordinates v)))
      (fun e x => F (u e x)) := by
    refine ⟨fun e => (heq e).state_energy (P.geometry.length_pos e).le
      (P.geometry.conductance_continuous e)
      (fun x hx => (P.geometry.conductance_pos e x hx).ne'), ?_, ?_⟩
    · intro e
      exact congrArg F ((P.geometry.coordinateEnergy φ).tail_value e)
    · intro e
      exact congrArg F ((P.geometry.coordinateEnergy φ).head_value e)
  apply P.graph_of_conservative_equations hκ _ _ _ _ _ k hu
  · intro e x
    change F (P.geometry.coordinateTest φ (P.geometry.edgePoint e x)) = F (u e x.val)
    rw [P.geometry.coordinateTest_edge]
  · intro e x
    change F₁ (P.geometry.coordinateTest φ (P.geometry.edgePoint e x)) *
      P.geometry.coordinateGenerator φ (P.geometry.edgePoint e x) +
      F₂ (P.geometry.coordinateTest φ (P.geometry.edgePoint e x)) *
      P.geometry.coordinateEnergyDensity φ (P.geometry.edgePoint e x) = k e x.val
    rw [P.geometry.coordinateTest_edge, P.geometry.coordinateGenerator_edge,
      P.geometry.coordinateEnergyDensity_edge]
    rfl
  · exact heq
  · exact hk
  · intro e
    change F₁ (u e 0) * P.geometry.coordinateEdgeFlux φ e 0 = 0 ∧
      F₁ (u e (P.geometry.length e)) * P.geometry.coordinateEdgeFlux φ e (P.geometry.length e) = 0
    simp only [(P.geometry.coordinateEdgeFlux_generator_endpoints φ e).1,
      (P.geometry.coordinateEdgeFlux_generator_endpoints φ e).2.1, mul_zero, and_self]

end TimeTraps.Analysis
