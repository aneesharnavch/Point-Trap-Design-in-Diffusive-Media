module

public import TimeTraps.Spectral.PhysicalState
public import TimeTraps.Spectral.LogDerivative

@[expose] public section

/-!
Exact logarithmic-derivative identities for an independently specified
positive physical eigenstate. The square identity holds for every original
interval H1 test function, with all physical trace values retained.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ}

def PositiveEigenstate.gapValue (E : PositiveEigenstate P ev) : Fin (n + 1) → ℝ → ℝ :=
  P.geometry.gapRestriction E.state

noncomputable def PositiveEigenstate.logSlope (E : PositiveEigenstate P ev)
    (e : Fin (n + 1)) (x : ℝ) : ℝ := E.slope e x / E.gapValue e x

theorem PositiveEigenstate.gap_energy (E : PositiveEigenstate P ev) (e : Fin (n + 1)) :
    IntervalEnergy (E.gapValue e) 0 (P.shooting.gap e) :=
  (P.geometry.restrict_energy E.energy).edge_energy e

theorem PositiveEigenstate.gap_positive (E : PositiveEigenstate P ev) (e : Fin (n + 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (P.shooting.gap e)) : 0 < E.gapValue e x :=
  E.positive _ (P.geometry.gap_point_mem e hx)

theorem PositiveEigenstate.gap_continuous (E : PositiveEigenstate P ev) (e : Fin (n + 1)) :
    ContinuousOn (E.gapValue e) (Icc (0 : ℝ) (P.shooting.gap e)) := by
  simpa only [uIcc_of_le (P.shooting.gap_pos e).le] using (E.gap_energy e).continuousOn

theorem PositiveEigenstate.gap_left (E : PositiveEigenstate P ev) (e : Fin (n + 1)) :
    E.gapValue e 0 = E.state (P.geometry.node e.castSucc) := by
  simp [gapValue, OrderedMedium.gapRestriction]

theorem PositiveEigenstate.gap_right (E : PositiveEigenstate P ev) (e : Fin (n + 1)) :
    E.gapValue e (P.shooting.gap e) = E.state (P.geometry.node e.succ) := by
  change E.state (P.geometry.node e.castSucc + (P.geometry.node e.succ - P.geometry.node e.castSucc)) = _
  rw [add_sub_cancel]

theorem PositiveEigenstate.gap_trap_left (E : PositiveEigenstate P ev) (i : Fin n) :
    E.gapValue i.castSucc (P.shooting.gap i.castSucc) = E.state (P.site i) := by
  rw [E.gap_right]
  change E.state (P.geometry.site i) = _
  rw [P.geometry_site]

theorem PositiveEigenstate.gap_trap_right (E : PositiveEigenstate P ev) (i : Fin n) :
    E.gapValue i.succ 0 = E.state (P.site i) := by
  rw [E.gap_left]
  change E.state (P.geometry.site i) = _
  rw [P.geometry_site]

theorem PositiveEigenstate.logSlope_continuous (E : PositiveEigenstate P ev) (e : Fin (n + 1)) :
    ContinuousOn (E.logSlope e) (Icc (0 : ℝ) (P.shooting.gap e)) :=
  (E.slope_continuous e).div (E.gap_continuous e) (fun _ hx => ne_of_gt (E.gap_positive e hx))

theorem PositiveEigenstate.logSlope_hasDerivAt (E : PositiveEigenstate P ev) (e : Fin (n + 1))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (P.shooting.gap e)) :
    HasDerivAt (E.logSlope e) (-ev / P.diffusivity - E.logSlope e x ^ 2) x := by
  have h := logarithmic_derivative (ne_of_gt (E.gap_positive e (Ioo_subset_Icc_self hx)))
    (E.state_derivative e x hx) (E.slope_derivative e x hx)
  unfold logSlope
  simpa only [neg_div] using h

theorem PositiveEigenstate.logSlope_left (E : PositiveEigenstate P ev) : E.logSlope 0 0 = 0 := by
  simp [logSlope, E.left_reflecting]

theorem PositiveEigenstate.logSlope_right (E : PositiveEigenstate P ev) :
    E.logSlope (Fin.last n) (P.shooting.gap (Fin.last n)) = 0 := by
  simp [logSlope, E.right_reflecting]

theorem PositiveEigenstate.logSlope_jump (E : PositiveEigenstate P ev) (i : Fin n) :
    P.diffusivity * (E.logSlope i.succ 0 - E.logSlope i.castSucc (P.shooting.gap i.castSucc)) = P.strength i := by
  have hp : E.state (P.site i) ≠ 0 := ne_of_gt (E.positive _ (Ioo_subset_Icc_self (P.site_interior i)))
  have hj := E.reaction_jump i
  unfold logSlope
  rw [E.gap_trap_left, E.gap_trap_right]
  field_simp [hp]
  nlinarith

noncomputable def PositiveEigenstate.gapRemainder (E : PositiveEigenstate P ev)
    (v : ℝ → ℝ) (e : Fin (n + 1)) : ℝ :=
  ∫ x in (0 : ℝ)..P.shooting.gap e,
    (deriv (P.geometry.gapRestriction v e) x - E.logSlope e x * P.geometry.gapRestriction v e x) ^ 2

theorem PositiveEigenstate.gapRemainder_nonneg (E : PositiveEigenstate P ev) (v : ℝ → ℝ)
    (e : Fin (n + 1)) : 0 ≤ E.gapRemainder v e :=
  intervalIntegral.integral_nonneg (P.shooting.gap_pos e).le (fun _ _ => sq_nonneg _)

theorem PositiveEigenstate.gap_square_identity (E : PositiveEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) (e : Fin (n + 1)) :
    (∫ x in (0 : ℝ)..P.shooting.gap e, deriv (P.geometry.gapRestriction v e) x ^ 2) -
      ev / P.diffusivity * (∫ x in (0 : ℝ)..P.shooting.gap e, P.geometry.gapRestriction v e x ^ 2) =
      E.gapRemainder v e + E.logSlope e (P.shooting.gap e) * v (P.geometry.node e.succ) ^ 2 -
        E.logSlope e 0 * v (P.geometry.node e.castSucc) ^ 2 := by
  have h := riccati_square_identity (a := ev / P.diffusivity) (P.shooting.gap_pos e).le
    ((P.geometry.restrict_energy hv).edge_energy e) (E.logSlope_continuous e)
    (fun x hx => by simpa only [neg_div] using E.logSlope_hasDerivAt e hx)
  simpa only [gapRemainder, OrderedMedium.gapRestriction, add_zero, SpectralProblem.shooting_gap,
    add_sub_cancel] using h

end TimeTraps.Spectral
