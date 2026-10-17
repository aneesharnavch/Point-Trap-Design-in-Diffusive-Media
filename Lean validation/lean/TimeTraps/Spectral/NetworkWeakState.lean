module

public import TimeTraps.Spectral.NetworkState

@[expose] public section

/-! The original network weak eigenvalue equation for every H1 test function. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] {P : SpectralNetwork V E} {ev : ℝ}

structure NetworkWeakEigenEquation (P : SpectralNetwork V E) (ev : ℝ)
    (U : V → ℝ) (u : E → ℝ → ℝ) : Prop where
  energy : GraphEnergy P.geometry U u
  weak_form : ∀ (W : V → ℝ) (w : E → ℝ → ℝ), GraphEnergy P.geometry W w →
    (∑ e, ∫ x in (0 : ℝ)..P.length e, P.diffusivity * deriv (u e) x * deriv (w e) x) +
      (∑ v, P.strength v * U v * W v) =
        ev * ∑ e, ∫ x in (0 : ℝ)..P.length e, u e x * w e x

omit [Fintype V] in
theorem PositiveNetworkEigenstate.edge_equation (F : PositiveNetworkEigenstate P ev) (e : E) :
    EdgeEquation (fun _ => P.diffusivity) (fun x => ev * F.state e x) 0 (P.length e)
      (F.state e) (fun x => P.diffusivity * F.slope e x) := by
  have hc : ContinuousOn (F.state e) (Icc 0 (P.length e)) := by
    simpa only [SpectralNetwork.geometry, uIcc_of_le (P.length_pos e).le] using
      (F.energy.edge_energy e).continuousOn
  refine ⟨hc, continuousOn_const.mul (F.slope_continuous e), ?_, ?_⟩
  · intro x hx
    rw [mul_div_cancel_left₀ _ (ne_of_gt P.diffusivity_pos)]
    exact F.state_derivative e x hx
  · intro x hx
    have h := (F.slope_derivative e x hx).const_mul P.diffusivity
    have he : P.diffusivity * (-(ev / P.diffusivity) * F.state e x) = -(ev * F.state e x) := by
      field_simp [ne_of_gt P.diffusivity_pos]
    change HasDerivAt (fun t => P.diffusivity * F.slope e t)
      (P.diffusivity * (-(ev / P.diffusivity) * F.state e x)) x at h
    rwa [he] at h

theorem PositiveNetworkEigenstate.to_weak (F : PositiveNetworkEigenstate P ev) :
    NetworkWeakEigenEquation P ev F.nodal F.state := by
  refine ⟨F.energy, ?_⟩
  intro W w hw
  have hc (e : E) : ContinuousOn (F.state e) (Icc 0 (P.length e)) := by
    simpa only [SpectralNetwork.geometry, uIcc_of_le (P.length_pos e).le] using
      (F.energy.edge_energy e).continuousOn
  have hedge (e : E) :
      (∫ x in (0 : ℝ)..P.length e, P.diffusivity * deriv (F.state e) x * deriv (w e) x) =
      ev * (∫ x in (0 : ℝ)..P.length e, F.state e x * w e x) +
        (P.diffusivity * F.slope e (P.length e) * W (P.head e) -
          P.diffusivity * F.slope e 0 * W (P.tail e)) := by
    have h := (F.edge_equation e).green_identity_energy (P.length_pos e).le
      (continuousOn_const.mul (hc e)) (fun _ _ => ne_of_gt P.diffusivity_pos) (hw.edge_energy e)
    have ht : w e 0 = W (P.tail e) := hw.tail_value e
    have hh : w e (P.length e) = W (P.head e) := hw.head_value e
    rw [ht, hh] at h
    change (∫ x in (0 : ℝ)..P.length e, P.diffusivity * deriv (F.state e) x * deriv (w e) x) =
      (∫ x in (0 : ℝ)..P.length e, ev * F.state e x * w e x) +
        P.diffusivity * F.slope e (P.length e) * W (P.head e) -
          P.diffusivity * F.slope e 0 * W (P.tail e) at h
    simp only [mul_assoc, intervalIntegral.integral_const_mul] at h ⊢
    linarith
  have hb : (∑ e, (P.diffusivity * F.slope e (P.length e) * W (P.head e) -
      P.diffusivity * F.slope e 0 * W (P.tail e))) = -(∑ v, P.strength v * F.nodal v * W v) := by
    rw [incidence_boundary_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    rw [← F.vertex_balance v]
    ring
  simp_rw [hedge]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hb]
  ring

theorem NetworkWeakEigenEquation.self_quadraticForm {U : V → ℝ} {u : E → ℝ → ℝ}
    (h : NetworkWeakEigenEquation P ev U u) : P.quadraticForm U u = ev * P.squareMass u := by
  have hs := h.weak_form U u h.energy
  simp only [← pow_two, mul_assoc, intervalIntegral.integral_const_mul, ← Finset.mul_sum] at hs
  exact hs

theorem SpectralNetwork.positive_weak_eigenstate_exists [Nonempty V] [Nonempty E]
    (P : SpectralNetwork V E) : ∃ ev : ℝ, 0 < ev ∧ ∃ U : V → ℝ, ∃ u : E → ℝ → ℝ,
      NetworkWeakEigenEquation P ev U u ∧ (∀ v, 0 < U v) ∧
        ∀ e x, x ∈ Icc 0 (P.length e) → 0 < u e x := by
  obtain ⟨ev, hev, ⟨F⟩⟩ := P.positive_eigenstate_exists
  exact ⟨ev, hev, F.nodal, F.state, F.to_weak, F.nodal_positive, F.positive⟩

end TimeTraps.Spectral
