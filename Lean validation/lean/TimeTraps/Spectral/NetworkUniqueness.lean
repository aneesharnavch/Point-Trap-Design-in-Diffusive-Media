module

public import TimeTraps.Spectral.NetworkRigidity

@[expose] public section

/-! Simplicity of the network ground state, for the original weak equation
and the independent Rayleigh minimum. No sign assumption is made on a rival. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]
  {P : SpectralNetwork V E} {ev : ℝ}

theorem NetworkWeakEigenEquation.eq_of_nodal_value {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : NetworkWeakEigenEquation P P.principalValue U u)
    (hw : NetworkWeakEigenEquation P P.principalValue W w)
    (v₀ : V) (h₀ : U v₀ = W v₀) :
    (∀ v, U v = W v) ∧ ∀ e, EqOn (u e) (w e) (Icc 0 (P.length e)) := by
  let : Nonempty V := ⟨v₀⟩
  obtain ⟨F⟩ := P.principal_eigenstate_exists
  have heu := F.proportional_of_quadraticForm_eq hu.energy hu.self_quadraticForm v₀
  have hew := F.proportional_of_quadraticForm_eq hw.energy hw.self_quadraticForm v₀
  constructor
  · intro v
    rw [heu.1 v, hew.1 v, h₀]
  · intro e x hx
    rw [heu.2 e hx, hew.2 e hx, h₀]

theorem NetworkWeakEigenEquation.positive_of_nodal_value_pos
    {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : NetworkWeakEigenEquation P P.principalValue U u) (v₀ : V) (h₀ : 0 < U v₀) :
    (∀ v, 0 < U v) ∧ ∀ e x, x ∈ Icc 0 (P.length e) → 0 < u e x := by
  let : Nonempty V := ⟨v₀⟩
  obtain ⟨F⟩ := P.principal_eigenstate_exists
  have he := F.proportional_of_quadraticForm_eq hu.energy hu.self_quadraticForm v₀
  have hc : 0 < U v₀ / F.nodal v₀ := div_pos h₀ (F.nodal_positive v₀)
  constructor
  · intro v
    rw [he.1 v]
    exact mul_pos hc (F.nodal_positive v)
  · intro e x hx
    rw [he.2 e hx]
    exact mul_pos hc (F.positive e x hx)

theorem PositiveNetworkEigenstate.eq_of_nodal_value
    (F : PositiveNetworkEigenstate P ev) {r : ℝ}
    (H : PositiveNetworkEigenstate P r) (v₀ : V) (h₀ : F.nodal v₀ = H.nodal v₀) :
    (∀ v, F.nodal v = H.nodal v) ∧
      ∀ e, EqOn (F.state e) (H.state e) (Icc 0 (P.length e)) := by
  have hf : NetworkWeakEigenEquation P P.principalValue F.nodal F.state := by
    rw [F.principalValue_eq]
    exact F.to_weak
  have hh : NetworkWeakEigenEquation P P.principalValue H.nodal H.state := by
    rw [H.principalValue_eq]
    exact H.to_weak
  exact hf.eq_of_nodal_value hh v₀ h₀

theorem SpectralNetwork.principal_ground_state_simple [Nonempty V]
    (P : SpectralNetwork V E) (v₀ : V) :
    ∃ F : PositiveNetworkEigenstate P P.principalValue,
      NetworkWeakEigenEquation P P.principalValue F.nodal F.state ∧
      (∀ W w, NetworkWeakEigenEquation P P.principalValue W w →
        ∃! c : ℝ, (∀ v, W v = c * F.nodal v) ∧
          ∀ e, EqOn (w e) (fun x => c * F.state e x) (Icc 0 (P.length e))) ∧
      ∀ W w, GraphEnergy P.geometry W w → 0 < P.squareMass w →
        P.quadraticForm W w / P.squareMass w = P.principalValue →
        ∃! c : ℝ, c ≠ 0 ∧ (∀ v, W v = c * F.nodal v) ∧
          ∀ e, EqOn (w e) (fun x => c * F.state e x) (Icc 0 (P.length e)) := by
  obtain ⟨F⟩ := P.principal_eigenstate_exists
  exact ⟨F, F.to_weak, fun _ _ hw => F.weak_state_unique_scalar hw v₀,
    fun _ _ hw hm hmin => F.rayleigh_minimizer_unique_scalar hw hm hmin v₀⟩

end TimeTraps.Spectral
