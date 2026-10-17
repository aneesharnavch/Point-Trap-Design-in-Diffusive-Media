module

public import TimeTraps.Spectral.NetworkOperatorSelfAdjointPhysical
public import TimeTraps.Analysis.CompactInverseDomainCharacterization

@[expose] public section

/-! The complete eigenbasis of the actual network L2 operator is
constructed from its compact positive inverse. Each spectral vector has
an actual vertex-continuous edge H1 representative. Positive reciprocal
eigenvalues escape every bounded interval, counting multiplicities. -/

namespace TimeTraps.Spectral

open Set Filter InnerProductSpace TimeTraps.Analysis TimeTraps.Graph
open scoped Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def SpectralNetwork.eigenbasis (P : SpectralNetwork V E) :
    HilbertBasis (CompactSpectralIndex P.operatorInverse) ℝ (GraphL2Product P.geometry) :=
  P.operatorCompactPositiveInverse.eigenbasis

noncomputable def SpectralNetwork.eigenstate (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) : GraphSobolevSpace P.geometry :=
  P.operatorSolution (i.1⁻¹ • P.eigenbasis i)

theorem SpectralNetwork.eigenstate_state (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) :
    graphSobolevSpaceStateL P.geometry (P.eigenstate i) = P.eigenbasis i := by
  change P.operatorInverse (i.1⁻¹ • P.eigenbasis i) = P.eigenbasis i
  rw [map_smul]
  exact P.operatorCompactPositiveInverse.reciprocal_eigen i

theorem SpectralNetwork.eigenstate_energy (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) :
    GraphEnergy P.geometry (P.operatorNodes (P.eigenstate i)) (P.operatorRep (P.eigenstate i)) :=
  P.operatorRep_energy (P.eigenstate i)

theorem SpectralNetwork.eigenvalue_positive (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) : 0 < i.1⁻¹ :=
  P.operatorCompactPositiveInverse.reciprocal_positive i

theorem SpectralNetwork.eigenvalues_grow (P : SpectralNetwork V E) :
    Tendsto (fun i : CompactSpectralIndex P.operatorInverse => i.1⁻¹) cofinite atTop :=
  P.operatorCompactPositiveInverse.reciprocals_tendsto_atTop

theorem SpectralNetwork.finite_eigenvalues_below (P : SpectralNetwork V E) (R : ℝ) :
    {i : CompactSpectralIndex P.operatorInverse | i.1⁻¹ ≤ R}.Finite :=
  P.operatorCompactPositiveInverse.finite_reciprocals_le R

theorem SpectralNetwork.eigenbasis_operator_graph (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) :
    (P.eigenbasis i, i.1⁻¹ • P.eigenbasis i) ∈ P.operator.graph := by
  rw [P.operator_graph_iff, map_smul]
  exact P.operatorCompactPositiveInverse.reciprocal_eigen i

theorem SpectralNetwork.eigenstate_weak (P : SpectralNetwork V E)
    (i : CompactSpectralIndex P.operatorInverse) (v : GraphSobolevSpace P.geometry) :
    P.operatorForm (P.eigenstate i) v = i.1⁻¹ *
      inner ℝ (graphSobolevSpaceStateL P.geometry (P.eigenstate i))
        (graphSobolevSpaceStateL P.geometry v) := by
  rw [P.eigenstate_state]
  change P.operatorForm (P.operatorSolution (i.1⁻¹ • P.eigenbasis i)) v = _
  rw [P.operatorSolution_spec, real_inner_smul_left]

end TimeTraps.Spectral
