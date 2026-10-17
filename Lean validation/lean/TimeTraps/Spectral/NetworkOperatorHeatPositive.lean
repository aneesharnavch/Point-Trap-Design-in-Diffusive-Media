module

public import TimeTraps.Spectral.NetworkOperatorHeatGenerator
public import TimeTraps.Spectral.NetworkOperatorRegularityDomain
public import TimeTraps.Analysis.CompactSpectralSemigroupSmoothingDerivative

@[expose] public section

/-! Every original edge L2 initial state evolves into the actual network
operator domain at positive time. Its time derivative satisfies the full
GraphEnergy heat equation, with the derived edge AC/L2 regularity and
Kirchhoff/contact laws. No regularity is required of the initial state. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.heat_mem_domain_of_pos (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) {t : ℝ} (ht : 0 < t) :
    P.heatCurve x t ∈ P.operator.domain :=
  P.operatorCompactPositiveInverse.heatCurve_mem_domain_of_pos x ht

theorem SpectralNetwork.heat_hasDerivAt_of_pos (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (P.heatCurve x)
      (-P.operator ⟨P.heatCurve x t, P.heat_mem_domain_of_pos x ht⟩) t :=
  P.operatorCompactPositiveInverse.heatCurve_hasDerivAt_of_pos x ht

theorem SpectralNetwork.heat_deriv_graph_of_pos (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) {t : ℝ} (ht : 0 < t) :
    (P.heatCurve x t, -deriv (P.heatCurve x) t) ∈ P.operator.graph :=
  P.operatorCompactPositiveInverse.heatCurve_graph_deriv_of_pos x ht

theorem SpectralNetwork.heat_deriv_norm_le (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) {t : ℝ} (ht : 0 < t) :
    ‖deriv (P.heatCurve x) t‖ ≤ ‖x‖ / t :=
  P.operatorCompactPositiveInverse.heatCurve_deriv_norm_le x ht

theorem SpectralNetwork.heat_physical_of_pos (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) {t : ℝ} (ht : 0 < t) :
    ∃ (U : V → ℝ) (u : E → ℝ → ℝ), GraphEnergy P.geometry U u ∧
      (∀ e, (P.heatCurve x t) e =ᵐ[volume.restrict (Ioo 0 (P.length e))] u e) ∧
      ∀ (W : V → ℝ) (w : E → ℝ → ℝ), GraphEnergy P.geometry W w →
        (∑ e, ∫ y in (0 : ℝ)..P.length e, P.diffusivity * deriv (u e) y * deriv (w e) y) +
          (∑ v, P.strength v * U v * W v) =
            ∑ e, ∫ y in (0 : ℝ)..P.length e, (-deriv (P.heatCurve x) t) e y * w e y :=
  (P.operator_graph_iff_full_test _ _).mp (P.heat_deriv_graph_of_pos x ht)

theorem SpectralNetwork.heat_strong_of_pos (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) {t : ℝ} (ht : 0 < t) :
    ∃ (U : V → ℝ) (u j : E → ℝ → ℝ),
      NetworkL2StrongEquation P (-deriv (P.heatCurve x) t) U u j ∧
        ∀ e, (P.heatCurve x t) e =ᵐ[volume.restrict (Ioo 0 (P.length e))] u e :=
  (P.operator_graph_iff_strong _ _).mp (P.heat_deriv_graph_of_pos x ht)

end TimeTraps.Spectral
