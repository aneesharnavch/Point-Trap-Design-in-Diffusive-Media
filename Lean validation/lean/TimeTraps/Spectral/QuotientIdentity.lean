module

public import TimeTraps.Spectral.GroundStateIdentity
public import TimeTraps.Interval.IntegralAssembly

@[expose] public section

/-!
The ground-state remainder equals the single physical integral
∫ φ² ((v/φ)')². Quotient differentiation is justified almost everywhere
for every H1 test function, and finite gap assembly proves integrability
on the whole original interval.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ}

noncomputable def PositiveEigenstate.quotientSquare (E : PositiveEigenstate P ev)
    (v : ℝ → ℝ) (x : ℝ) : ℝ := E.state x ^ 2 * deriv (fun t => v t / E.state t) x ^ 2

theorem PositiveEigenstate.quotient_gap_ae (E : PositiveEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) (e : Fin (n + 1)) :
    (fun x => (deriv (P.geometry.gapRestriction v e) x - E.logSlope e x * P.geometry.gapRestriction v e x) ^ 2)
      =ᵐ[volume.restrict (uIoc (0 : ℝ) (P.shooting.gap e))]
      (fun x => E.quotientSquare v (P.geometry.node e.castSucc + x)) := by
  have hvg := (P.geometry.restrict_energy hv).edge_energy e
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [hvg.absolutelyContinuous.ae_differentiableAt, volume.ae_ne (P.shooting.gap e)]
    with x hdx hxr hx
  have hxoc : x ∈ Ioc (0 : ℝ) (P.shooting.gap e) := by
    simpa only [uIoc_of_le (P.shooting.gap_pos e).le] using hx
  have hxoo : x ∈ Ioo (0 : ℝ) (P.shooting.gap e) := ⟨hxoc.1, lt_of_le_of_ne hxoc.2 hxr⟩
  have hp := ne_of_gt (E.gap_positive e (Ioo_subset_Icc_self hxoo))
  have hdu : HasDerivAt (E.gapValue e) (E.slope e x) x := E.state_derivative e x hxoo
  have hdiv := (hdx (uIoc_subset_uIcc hx)).hasDerivAt.fun_div hdu hp
  have he : deriv (fun t => v t / E.state t) (P.geometry.node e.castSucc + x) =
      (deriv (P.geometry.gapRestriction v e) x * E.gapValue e x -
        P.geometry.gapRestriction v e x * E.slope e x) / E.gapValue e x ^ 2 := by
    rw [← deriv_comp_const_add (fun t => v t / E.state t) (P.geometry.node e.castSucc) x]
    exact hdiv.deriv
  unfold quotientSquare
  rw [he]
  change (deriv (P.geometry.gapRestriction v e) x - E.slope e x / E.gapValue e x * P.geometry.gapRestriction v e x) ^ 2 =
    E.gapValue e x ^ 2 * ((deriv (P.geometry.gapRestriction v e) x * E.gapValue e x -
      P.geometry.gapRestriction v e x * E.slope e x) / E.gapValue e x ^ 2) ^ 2
  field_simp [hp]

theorem PositiveEigenstate.quotientSquare_integrable (E : PositiveEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) : IntervalIntegrable (E.quotientSquare v) volume 0 P.length := by
  apply P.geometry.integrable_of_gaps
  intro e
  have hq : ContinuousOn (E.logSlope e) (uIcc (0 : ℝ) (P.shooting.gap e)) := by
    simpa only [uIcc_of_le (P.shooting.gap_pos e).le] using E.logSlope_continuous e
  have hi := shifted_square_integrable ((P.geometry.restrict_energy hv).edge_energy e) hq
  exact hi.congr_ae (E.quotient_gap_ae hv e)

theorem PositiveEigenstate.gapRemainder_quotient (E : PositiveEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) (e : Fin (n + 1)) :
    E.gapRemainder v e = ∫ x in (0 : ℝ)..P.shooting.gap e,
      E.quotientSquare v (P.geometry.node e.castSucc + x) :=
  intervalIntegral.integral_congr_ae_restrict (E.quotient_gap_ae hv e)

theorem PositiveEigenstate.quotient_integral_identity (E : PositiveEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) :
    P.quadraticForm v - ev * P.squareMass v =
      P.diffusivity * (∫ x in (0 : ℝ)..P.length, E.state x ^ 2 * deriv (fun t => v t / E.state t) x ^ 2) := by
  rw [E.ground_state_identity hv]
  simp_rw [E.gapRemainder_quotient hv]
  have h := P.geometry.integral_gap_sum (E.quotientSquare_integrable hv)
  change (∑ e, ∫ x in (0 : ℝ)..P.shooting.gap e, E.quotientSquare v (P.geometry.node e.castSucc + x)) =
    ∫ x in (0 : ℝ)..P.length, E.quotientSquare v x at h
  rw [h]
  rfl

end TimeTraps.Spectral
