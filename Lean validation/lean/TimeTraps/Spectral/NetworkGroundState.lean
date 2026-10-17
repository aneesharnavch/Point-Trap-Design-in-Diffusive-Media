module

public import TimeTraps.Spectral.NetworkWeakState
public import TimeTraps.Spectral.LogDerivative

@[expose] public section

/-! The network ground-state square identity for all matching H1 test functions.
Incidence cancellation includes both ends of every loop and the circle's wrap. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] {P : SpectralNetwork V E} {ev : ℝ}

noncomputable def PositiveNetworkEigenstate.logSlope (F : PositiveNetworkEigenstate P ev)
    (e : E) (x : ℝ) : ℝ := F.slope e x / F.state e x

noncomputable def PositiveNetworkEigenstate.edgeRemainder (F : PositiveNetworkEigenstate P ev)
    (w : E → ℝ → ℝ) (e : E) : ℝ :=
  ∫ x in (0 : ℝ)..P.length e, (deriv (w e) x - F.logSlope e x * w e x) ^ 2

omit [Fintype V] in
theorem PositiveNetworkEigenstate.edge_continuous (F : PositiveNetworkEigenstate P ev) (e : E) :
    ContinuousOn (F.state e) (Icc 0 (P.length e)) := by
  simpa only [SpectralNetwork.geometry, uIcc_of_le (P.length_pos e).le] using
    (F.energy.edge_energy e).continuousOn

omit [Fintype V] in
theorem PositiveNetworkEigenstate.logSlope_continuous (F : PositiveNetworkEigenstate P ev) (e : E) :
    ContinuousOn (F.logSlope e) (Icc 0 (P.length e)) :=
  (F.slope_continuous e).div (F.edge_continuous e) (fun x hx => ne_of_gt (F.positive e x hx))

omit [Fintype V] in
theorem PositiveNetworkEigenstate.logSlope_hasDerivAt (F : PositiveNetworkEigenstate P ev)
    (e : E) {x : ℝ} (hx : x ∈ Ioo 0 (P.length e)) :
    HasDerivAt (F.logSlope e) (-(ev / P.diffusivity) - F.logSlope e x ^ 2) x :=
  logarithmic_derivative (ne_of_gt (F.positive e x (Ioo_subset_Icc_self hx)))
    (F.state_derivative e x hx) (F.slope_derivative e x hx)

omit [Fintype V] in
theorem PositiveNetworkEigenstate.edgeRemainder_nonneg (F : PositiveNetworkEigenstate P ev)
    (w : E → ℝ → ℝ) (e : E) : 0 ≤ F.edgeRemainder w e :=
  intervalIntegral.integral_nonneg (P.length_pos e).le (fun _ _ => sq_nonneg _)

theorem PositiveNetworkEigenstate.boundary_cancellation (F : PositiveNetworkEigenstate P ev)
    {W : V → ℝ} {w : E → ℝ → ℝ} (hw : GraphEnergy P.geometry W w) :
    (∑ e, P.diffusivity * (F.logSlope e (P.length e) * w e (P.length e) ^ 2 -
      F.logSlope e 0 * w e 0 ^ 2)) = -(∑ v, P.strength v * W v ^ 2) := by
  have he : (∑ e, P.diffusivity * (F.logSlope e (P.length e) * w e (P.length e) ^ 2 -
      F.logSlope e 0 * w e 0 ^ 2)) =
      ∑ e, ((P.diffusivity * F.slope e (P.length e)) * (W (P.head e) ^ 2 / F.nodal (P.head e)) -
        (P.diffusivity * F.slope e 0) * (W (P.tail e) ^ 2 / F.nodal (P.tail e))) := by
    apply Finset.sum_congr rfl
    intro e _
    unfold logSlope
    have ht : w e 0 = W (P.tail e) := hw.tail_value e
    have hh : w e (P.length e) = W (P.head e) := hw.head_value e
    have hft : F.state e 0 = F.nodal (P.tail e) := F.energy.tail_value e
    have hfh : F.state e (P.length e) = F.nodal (P.head e) := F.energy.head_value e
    rw [ht, hh, hft, hfh]
    ring
  rw [he, incidence_boundary_sum P.tail P.head
    (fun e => P.diffusivity * F.slope e 0)
    (fun e => P.diffusivity * F.slope e (P.length e)) (fun v => W v ^ 2 / F.nodal v)]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [← F.vertex_balance v]
  field_simp [ne_of_gt (F.nodal_positive v)]

theorem PositiveNetworkEigenstate.ground_state_identity (F : PositiveNetworkEigenstate P ev)
    {W : V → ℝ} {w : E → ℝ → ℝ} (hw : GraphEnergy P.geometry W w) :
    P.quadraticForm W w - ev * P.squareMass w = P.diffusivity * ∑ e, F.edgeRemainder w e := by
  have he (e : E) :
      P.diffusivity * (∫ x in (0 : ℝ)..P.length e, deriv (w e) x ^ 2) -
        ev * (∫ x in (0 : ℝ)..P.length e, w e x ^ 2) =
      P.diffusivity * F.edgeRemainder w e +
        P.diffusivity * (F.logSlope e (P.length e) * w e (P.length e) ^ 2 -
          F.logSlope e 0 * w e 0 ^ 2) := by
    have h := riccati_square_identity (P.length_pos e).le (hw.edge_energy e)
      (F.logSlope_continuous e) (fun _ hx => F.logSlope_hasDerivAt e hx)
    calc
      _ = P.diffusivity * ((∫ x in (0 : ℝ)..P.length e, deriv (w e) x ^ 2) -
          ev / P.diffusivity * (∫ x in (0 : ℝ)..P.length e, w e x ^ 2)) := by
        field_simp [ne_of_gt P.diffusivity_pos]
      _ = _ := by rw [h]; unfold edgeRemainder; ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun e _ => he e)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, F.boundary_cancellation hw] at hs
  simp only [← Finset.mul_sum] at hs
  unfold SpectralNetwork.quadraticForm SpectralNetwork.squareMass
  linarith

theorem PositiveNetworkEigenstate.quadraticForm_lower (F : PositiveNetworkEigenstate P ev)
    {W : V → ℝ} {w : E → ℝ → ℝ} (hw : GraphEnergy P.geometry W w) :
    ev * P.squareMass w ≤ P.quadraticForm W w := by
  have h := F.ground_state_identity hw
  have hn : 0 ≤ P.diffusivity * ∑ e, F.edgeRemainder w e :=
    mul_nonneg P.diffusivity_pos.le (Finset.sum_nonneg fun e _ => F.edgeRemainder_nonneg w e)
  linarith

end TimeTraps.Spectral
