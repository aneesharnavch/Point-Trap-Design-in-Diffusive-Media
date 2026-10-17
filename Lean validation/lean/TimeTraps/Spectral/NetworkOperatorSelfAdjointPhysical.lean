module

public import TimeTraps.Spectral.NetworkOperatorSelfAdjoint

@[expose] public section

/-! Exact physical graph of the actual self-adjoint network operator.
The continuous vertex values are recovered from the original edge H1
states, and the forcing is tested against every original GraphEnergy
function. Equality with an L2 state is required on every physical edge
almost everywhere; loops and parallel edges are retained. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.operator_graph_iff_physical (P : SpectralNetwork V E)
    (f : GraphL2Product P.geometry) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) :
    (graphSobolevSpaceStateL P.geometry (graphSobolevSpaceOfEnergy P.geometry hu), f)
      ∈ P.operator.graph ↔ NetworkL2WeakEquation P f U u := by
  rw [P.operator_graph_iff, P.operatorInverse_apply]
  constructor
  · intro h
    refine ⟨hu, (P.operatorWeak_iff f hu).mp ?_⟩
    have hs : graphSobolevSpaceOfEnergy P.geometry hu = P.operatorSolution f :=
      (graphSobolevSpaceStateL_injective P.geometry h).symm
    rw [hs]
    simpa only [P.operatorLoad_apply] using P.operatorSolution_spec f
  · intro h
    rw [h.to_operatorSolution]

theorem SpectralNetwork.operator_graph_iff_exists_physical (P : SpectralNetwork V E)
    (g f : GraphL2Product P.geometry) :
    (g, f) ∈ P.operator.graph ↔ ∃ (U : V → ℝ) (u : E → ℝ → ℝ),
      NetworkL2WeakEquation P f U u ∧
        ∀ e, g e =ᵐ[volume.restrict (Ioo 0 (P.length e))] u e := by
  rw [P.operator_graph_iff]
  constructor
  · intro h
    refine ⟨P.operatorNodes (P.operatorSolution f), P.operatorRep (P.operatorSolution f),
      P.operatorSolution_physical f, ?_⟩
    intro e
    rw [← h, P.operatorInverse_apply]
    exact graphSobolevRepresentative_state_ae P.geometry (P.operatorSolution f).val e
  · rintro ⟨U, u, hu, he⟩
    rw [P.operatorInverse_apply, ← hu.to_operatorSolution]
    apply PiLp.ext
    intro e
    exact Lp.ext ((graphSobolevSpaceOfEnergy_state_ae P.geometry hu.energy e).trans (he e).symm)

theorem SpectralNetwork.operator_graph_iff_full_test (P : SpectralNetwork V E)
    (g f : GraphL2Product P.geometry) :
    (g, f) ∈ P.operator.graph ↔ ∃ (U : V → ℝ) (u : E → ℝ → ℝ),
      GraphEnergy P.geometry U u ∧
      (∀ e, g e =ᵐ[volume.restrict (Ioo 0 (P.length e))] u e) ∧
      ∀ (W : V → ℝ) (w : E → ℝ → ℝ), GraphEnergy P.geometry W w →
        (∑ e, ∫ x in (0 : ℝ)..P.length e, P.diffusivity * deriv (u e) x * deriv (w e) x) +
          (∑ v, P.strength v * U v * W v) =
            ∑ e, ∫ x in (0 : ℝ)..P.length e, (f e) x * w e x := by
  rw [P.operator_graph_iff_exists_physical]
  constructor
  · rintro ⟨U, u, hu, he⟩
    exact ⟨U, u, hu.energy, he, hu.weak_form⟩
  · rintro ⟨U, u, hu, he, hw⟩
    exact ⟨U, u, ⟨hu, hw⟩, he⟩

end TimeTraps.Spectral
