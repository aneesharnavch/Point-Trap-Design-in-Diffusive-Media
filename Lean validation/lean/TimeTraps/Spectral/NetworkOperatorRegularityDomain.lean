module

public import TimeTraps.Spectral.NetworkOperatorRegularityStrong

@[expose] public section

/-! Full strong graph and domain characterization of the actual network
operator on its independent edge L2 Hilbert space. Vertex continuity and
global GraphEnergy membership follow from the edge AC/L2 certificates
and endpoint equalities, rather than being extra premises. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.operator_graph_iff_strong (P : SpectralNetwork V E)
    (g f : GraphL2Product P.geometry) :
    (g, f) ∈ P.operator.graph ↔ ∃ (U : V → ℝ) (u j : E → ℝ → ℝ),
      NetworkL2StrongEquation P f U u j ∧
        ∀ e, g e =ᵐ[volume.restrict (Ioo 0 (P.length e))] u e := by
  rw [P.operator_graph_iff_exists_physical]
  constructor
  · rintro ⟨U, u, hu, he⟩
    obtain ⟨j, hj⟩ := hu.exists_strong
    exact ⟨U, u, j, hj, he⟩
  · rintro ⟨U, u, j, hj, he⟩
    exact ⟨U, u, hj.to_weak, he⟩

theorem SpectralNetwork.operator_domain_iff_strong (P : SpectralNetwork V E)
    (g : GraphL2Product P.geometry) :
    g ∈ P.operator.domain ↔ ∃ (f : GraphL2Product P.geometry) (U : V → ℝ)
      (u j : E → ℝ → ℝ), NetworkL2StrongEquation P f U u j ∧
        ∀ e, g e =ᵐ[volume.restrict (Ioo 0 (P.length e))] u e := by
  rw [LinearPMap.mem_domain_iff]
  simp_rw [P.operator_graph_iff_strong]

theorem SpectralNetwork.operatorSolution_strong (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) : ∃ j : E → ℝ → ℝ,
      NetworkL2StrongEquation P f (P.operatorNodes (P.operatorSolution f))
        (P.operatorRep (P.operatorSolution f)) j :=
  (P.operatorSolution_physical f).exists_strong

end TimeTraps.Spectral
