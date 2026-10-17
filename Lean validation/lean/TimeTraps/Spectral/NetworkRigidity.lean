module

public import TimeTraps.Spectral.NetworkQuotient

@[expose] public section

/-! Equality in the network Rayleigh bound. Matching traces and incidence
connectivity identify the constants on all arcs, including loops. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] {P : SpectralNetwork V E} {ev : ℝ}

theorem PositiveNetworkEigenstate.nodal_ratio_edge (F : PositiveNetworkEigenstate P ev)
    {W : V → ℝ} {w : E → ℝ → ℝ} (hw : GraphEnergy P.geometry W w)
    (he : P.quadraticForm W w = ev * P.squareMass w) (e : E) :
    W (P.tail e) / F.nodal (P.tail e) = W (P.head e) / F.nodal (P.head e) := by
  have hc := F.proportional_on_edge_of_remainder_zero hw e
    (F.edgeRemainder_zero_of_quadraticForm_eq hw he e)
  have hh := hc ⟨(P.length_pos e).le, le_rfl⟩
  have hwhead : w e (P.length e) = W (P.head e) := hw.head_value e
  have hfhead : F.state e (P.length e) = F.nodal (P.head e) := F.energy.head_value e
  dsimp only at hh
  rw [hwhead, hfhead] at hh
  exact ((div_eq_iff (ne_of_gt (F.nodal_positive (P.head e)))).mpr hh).symm

theorem PositiveNetworkEigenstate.nodal_ratio_constant (F : PositiveNetworkEigenstate P ev)
    {W : V → ℝ} {w : E → ℝ → ℝ} (hw : GraphEnergy P.geometry W w)
    (he : P.quadraticForm W w = ev * P.squareMass w) (v z : V) :
    W v / F.nodal v = W z / F.nodal z := by
  induction P.connected v z with
  | rel v z h =>
    obtain ⟨e, rfl, rfl⟩ := h
    exact F.nodal_ratio_edge hw he e
  | refl v => rfl
  | symm v z _ ih => exact ih.symm
  | trans v z t _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem PositiveNetworkEigenstate.proportional_of_quadraticForm_eq
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) (he : P.quadraticForm W w = ev * P.squareMass w)
    (v₀ : V) :
    (∀ v, W v = (W v₀ / F.nodal v₀) * F.nodal v) ∧
      ∀ e, EqOn (w e) (fun x => (W v₀ / F.nodal v₀) * F.state e x) (Icc 0 (P.length e)) := by
  constructor
  · intro v
    exact (div_eq_iff (ne_of_gt (F.nodal_positive v))).mp (F.nodal_ratio_constant hw he v v₀)
  · intro e
    have hc := F.proportional_on_edge_of_remainder_zero hw e
      (F.edgeRemainder_zero_of_quadraticForm_eq hw he e)
    rwa [F.nodal_ratio_constant hw he (P.tail e) v₀] at hc

theorem PositiveNetworkEigenstate.unique_scalar_of_quadraticForm_eq
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) (he : P.quadraticForm W w = ev * P.squareMass w)
    (v₀ : V) :
    ∃! c : ℝ, (∀ v, W v = c * F.nodal v) ∧
      ∀ e, EqOn (w e) (fun x => c * F.state e x) (Icc 0 (P.length e)) := by
  refine ⟨W v₀ / F.nodal v₀, F.proportional_of_quadraticForm_eq hw he v₀, ?_⟩
  intro c hc
  exact (eq_div_iff (ne_of_gt (F.nodal_positive v₀))).mpr (hc.1 v₀).symm

omit [Fintype V] in
theorem PositiveNetworkEigenstate.squareMass_of_eq_scalar (F : PositiveNetworkEigenstate P ev)
    {w : E → ℝ → ℝ} {c : ℝ}
    (h : ∀ e, EqOn (w e) (fun x => c * F.state e x) (Icc 0 (P.length e))) :
    P.squareMass w = c ^ 2 * P.squareMass F.state := by
  unfold SpectralNetwork.squareMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  change w e x ^ 2 = c ^ 2 * F.state e x ^ 2
  rw [h e (by simpa only [uIcc_of_le (P.length_pos e).le] using hx), mul_pow]

theorem PositiveNetworkEigenstate.unique_nonzero_scalar_of_quadraticForm_eq
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) (hm : 0 < P.squareMass w)
    (he : P.quadraticForm W w = ev * P.squareMass w) (v₀ : V) :
    ∃! c : ℝ, c ≠ 0 ∧ (∀ v, W v = c * F.nodal v) ∧
      ∀ e, EqOn (w e) (fun x => c * F.state e x) (Icc 0 (P.length e)) := by
  obtain ⟨c, hc, huniq⟩ := F.unique_scalar_of_quadraticForm_eq hw he v₀
  have hcn : c ≠ 0 := by
    intro hz
    have hmass := F.squareMass_of_eq_scalar hc.2
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hmass
    exact (ne_of_gt hm) hmass
  exact ⟨c, ⟨hcn, hc⟩, fun d hd => huniq d hd.2⟩

theorem PositiveNetworkEigenstate.rayleigh_minimizer_unique_scalar [Nonempty E]
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) (hm : 0 < P.squareMass w)
    (hmin : P.quadraticForm W w / P.squareMass w = P.principalValue) (v₀ : V) :
    ∃! c : ℝ, c ≠ 0 ∧ (∀ v, W v = c * F.nodal v) ∧
      ∀ e, EqOn (w e) (fun x => c * F.state e x) (Icc 0 (P.length e)) := by
  apply F.unique_nonzero_scalar_of_quadraticForm_eq hw hm _ v₀
  exact (div_eq_iff (ne_of_gt hm)).mp (hmin.trans F.principalValue_eq)

theorem PositiveNetworkEigenstate.weak_state_unique_scalar
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : NetworkWeakEigenEquation P ev W w) (v₀ : V) :
    ∃! c : ℝ, (∀ v, W v = c * F.nodal v) ∧
      ∀ e, EqOn (w e) (fun x => c * F.state e x) (Icc 0 (P.length e)) :=
  F.unique_scalar_of_quadraticForm_eq hw.energy hw.self_quadraticForm v₀

end TimeTraps.Spectral
