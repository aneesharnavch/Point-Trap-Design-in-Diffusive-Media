module

public import TimeTraps.Spectral.NetworkRayleigh
public import TimeTraps.Analysis.PositiveQuotient

@[expose] public section

/-! Exact quotient energy on every network arc. Equality in the ground-state
bound forces a constant quotient on each entire closed arc. -/

namespace TimeTraps.Spectral

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] {P : SpectralNetwork V E} {ev : ℝ}

noncomputable def PositiveNetworkEigenstate.quotientSquare
    (F : PositiveNetworkEigenstate P ev) (w : E → ℝ → ℝ) (e : E) (x : ℝ) : ℝ :=
  F.state e x ^ 2 * deriv (fun t => w e t / F.state e t) x ^ 2

omit [Fintype V] in
theorem PositiveNetworkEigenstate.edge_quotient_ae (F : PositiveNetworkEigenstate P ev)
    {W : V → ℝ} {w : E → ℝ → ℝ} (hw : GraphEnergy P.geometry W w) (e : E) :
    (fun x => (deriv (w e) x - F.logSlope e x * w e x) ^ 2)
      =ᵐ[volume.restrict (uIoc (0 : ℝ) (P.length e))] F.quotientSquare w e := by
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [(hw.edge_energy e).absolutelyContinuous.ae_differentiableAt,
    volume.ae_ne (P.length e)] with x hdx hxr hx
  have hxoc : x ∈ Ioc (0 : ℝ) (P.length e) := by
    simpa only [uIoc_of_le (P.length_pos e).le] using hx
  have hxoo : x ∈ Ioo (0 : ℝ) (P.length e) := ⟨hxoc.1, lt_of_le_of_ne hxoc.2 hxr⟩
  have hp := ne_of_gt (F.positive e x (Ioo_subset_Icc_self hxoo))
  have hdiv := (hdx (uIoc_subset_uIcc hx)).hasDerivAt.fun_div
    (F.state_derivative e x hxoo) hp
  unfold quotientSquare logSlope
  rw [hdiv.deriv]
  field_simp [hp]

omit [Fintype V] in
theorem PositiveNetworkEigenstate.quotientSquare_integrable
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) (e : E) :
    IntervalIntegrable (F.quotientSquare w e) volume 0 (P.length e) := by
  have hq : ContinuousOn (F.logSlope e) (uIcc (0 : ℝ) (P.length e)) := by
    simpa only [uIcc_of_le (P.length_pos e).le] using F.logSlope_continuous e
  exact (shifted_square_integrable (hw.edge_energy e) hq).congr_ae (F.edge_quotient_ae hw e)

omit [Fintype V] in
theorem PositiveNetworkEigenstate.edgeRemainder_quotient
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) (e : E) :
    F.edgeRemainder w e = ∫ x in (0 : ℝ)..P.length e, F.quotientSquare w e x :=
  intervalIntegral.integral_congr_ae_restrict (F.edge_quotient_ae hw e)

theorem PositiveNetworkEigenstate.quotient_energy_identity
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) :
    P.quadraticForm W w - ev * P.squareMass w =
      P.diffusivity * ∑ e, ∫ x in (0 : ℝ)..P.length e,
        F.state e x ^ 2 * deriv (fun t => w e t / F.state e t) x ^ 2 := by
  rw [F.ground_state_identity hw]
  simp_rw [F.edgeRemainder_quotient hw]
  rfl

theorem PositiveNetworkEigenstate.edgeRemainder_zero_of_quadraticForm_eq
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) (he : P.quadraticForm W w = ev * P.squareMass w)
    (e : E) : F.edgeRemainder w e = 0 := by
  have h := F.ground_state_identity hw
  rw [he, sub_self] at h
  have hs : (∑ j, F.edgeRemainder w j) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt P.diffusivity_pos)
  apply le_antisymm _ (F.edgeRemainder_nonneg w e)
  calc
    F.edgeRemainder w e ≤ ∑ j, F.edgeRemainder w j :=
      Finset.single_le_sum (fun j _ => F.edgeRemainder_nonneg w j) (Finset.mem_univ e)
    _ = 0 := hs

omit [Fintype V] in
theorem PositiveNetworkEigenstate.proportional_on_edge_of_remainder_zero
    (F : PositiveNetworkEigenstate P ev) {W : V → ℝ} {w : E → ℝ → ℝ}
    (hw : GraphEnergy P.geometry W w) (e : E) (hz : F.edgeRemainder w e = 0) :
    EqOn (w e) (fun x => (W (P.tail e) / F.nodal (P.tail e)) * F.state e x)
      (Icc 0 (P.length e)) := by
  have hp : ∀ x ∈ uIcc (0 : ℝ) (P.length e), 0 < F.state e x := by
    intro x hx
    exact F.positive e x (by simpa only [uIcc_of_le (P.length_pos e).le] using hx)
  have hq := interval_absolutelyContinuous_div (hw.edge_energy e).absolutelyContinuous
    (F.energy.edge_energy e).absolutelyContinuous hp
  have hi := F.quotientSquare_integrable hw e
  rw [F.edgeRemainder_quotient hw e] at hz
  have hc := interval_absolutelyContinuous_constant_of_weighted_derivative_zero hq
    (P.length_pos e).le (fun x hx => sq_pos_of_pos (F.positive e x hx)) hi hz
  intro x hx
  apply (div_eq_iff (ne_of_gt (F.positive e x hx))).mp
  have ht : w e 0 = W (P.tail e) := hw.tail_value e
  have hft : F.state e 0 = F.nodal (P.tail e) := F.energy.tail_value e
  simpa only [ht, hft] using hc x hx

end TimeTraps.Spectral
