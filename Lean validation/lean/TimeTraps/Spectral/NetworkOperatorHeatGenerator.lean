module

public import TimeTraps.Spectral.NetworkOperatorHeat

@[expose] public section

/-! The exact strong right generator on the whole network L2 space is
the negative of the actual self-adjoint operator. The converse forces
membership in its full domain, and the physical version retains every
original GraphEnergy test. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.heat_generator_iff_graph (P : SpectralNetwork V E)
    (x f : GraphL2Product P.geometry) :
    HasDerivWithinAt (P.heatCurve x) (-f) (Ici 0) 0 ↔ (x, f) ∈ P.operator.graph := by
  change HasDerivWithinAt (P.operatorCompactPositiveInverse.heatCurve x) (-f) (Ici 0) 0 ↔ _
  rw [P.operatorCompactPositiveInverse.heatCurve_generator_iff]
  constructor
  · rintro ⟨hx, he⟩
    have hf : f = P.operator ⟨x, hx⟩ := neg_injective he
    rw [P.operator_graph_iff, hf]
    exact inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective ⟨x, hx⟩
  · intro he
    have ht := (P.operator_graph_iff x f).mp he
    have hx : x ∈ P.operator.domain := ⟨f, ht⟩
    refine ⟨hx, ?_⟩
    apply congrArg Neg.neg
    apply P.operatorInverse_injective
    exact ht.trans
      (inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective ⟨x, hx⟩).symm

theorem SpectralNetwork.heat_generator_iff_physical (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) :
    HasDerivWithinAt (P.heatCurve
      (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu)))
        (-f) (Ici 0) 0 ↔ NetworkL2WeakEquation P f U u :=
  (P.heat_generator_iff_graph _ f).trans (P.operator_graph_iff_physical f hu)

theorem SpectralNetwork.heat_right_differentiable_iff (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) :
    DifferentiableWithinAt ℝ (P.heatCurve x) (Ici 0) 0 ↔ x ∈ P.operator.domain :=
  P.operatorCompactPositiveInverse.heatCurve_right_differentiable_iff x

end TimeTraps.Spectral
