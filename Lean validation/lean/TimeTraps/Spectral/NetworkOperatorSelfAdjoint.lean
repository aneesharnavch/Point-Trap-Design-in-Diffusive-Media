module

public import TimeTraps.Spectral.NetworkOperatorInverse
public import TimeTraps.Analysis.InverseOperatorAdjoint

@[expose] public section

/-! The actual unbounded network operator is the inverse of the compact
L2 solution map. Its dense domain, closedness and self-adjointness follow
for the independently constructed edge L2 Hilbert product. Its graph is
exactly the full vertex-continuous Hilbert variational equation. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def SpectralNetwork.operator (P : SpectralNetwork V E) :
    GraphL2Product P.geometry →ₗ.[ℝ] GraphL2Product P.geometry :=
  inverseOperator P.operatorInverse P.operatorInverse_injective

theorem SpectralNetwork.operator_domain (P : SpectralNetwork V E) :
    P.operator.domain = P.operatorInverse.range := rfl

theorem SpectralNetwork.operator_dense_domain (P : SpectralNetwork V E) :
    Dense (P.operator.domain : Set (GraphL2Product P.geometry)) :=
  inverseOperator_dense_domain P.operatorInverse P.operatorInverse_injective
    P.operatorInverse_symmetric

theorem SpectralNetwork.operator_closed (P : SpectralNetwork V E) :
    P.operator.IsClosed :=
  inverseOperator_isClosed P.operatorInverse P.operatorInverse_injective

theorem SpectralNetwork.operator_selfAdjoint (P : SpectralNetwork V E) :
    IsSelfAdjoint P.operator :=
  inverseOperator_isSelfAdjoint P.operatorInverse P.operatorInverse_injective
    P.operatorInverse_symmetric

theorem SpectralNetwork.operator_graph_iff (P : SpectralNetwork V E)
    (u f : GraphL2Product P.geometry) :
    (u, f) ∈ P.operator.graph ↔ P.operatorInverse f = u :=
  inverseOperator_graph_iff P.operatorInverse P.operatorInverse_injective u f

theorem SpectralNetwork.operator_graph_iff_hilbert (P : SpectralNetwork V E)
    (u f : GraphL2Product P.geometry) :
    (u, f) ∈ P.operator.graph ↔ ∃ v : GraphSobolevSpace P.geometry,
      graphSobolevSpaceStateL P.geometry v = u ∧ ∀ w : GraphSobolevSpace P.geometry,
        P.operatorForm v w = inner ℝ f (graphSobolevSpaceStateL P.geometry w) := by
  rw [P.operator_graph_iff]
  constructor
  · intro h
    exact ⟨P.operatorSolution f, h, P.operatorSolution_spec f⟩
  · rintro ⟨v, hv, he⟩
    rw [(P.operatorSolution_eq_iff f v).mpr he] at hv
    exact hv

theorem SpectralNetwork.operator_positive (P : SpectralNetwork V E)
    (u : P.operator.domain) (hu : (u : GraphL2Product P.geometry) ≠ 0) :
    0 < inner ℝ (u : GraphL2Product P.geometry) (P.operator u) := by
  have hi : P.operatorInverse (P.operator u) = u :=
    inverseOperator_right_inverse P.operatorInverse P.operatorInverse_injective u
  have hf : P.operator u ≠ 0 := by
    intro h
    rw [h, map_zero] at hi
    exact hu hi.symm
  have hp := P.operatorInverse_positive hf
  rw [hi] at hp
  exact hp.trans_eq (real_inner_comm _ _)

end TimeTraps.Spectral
