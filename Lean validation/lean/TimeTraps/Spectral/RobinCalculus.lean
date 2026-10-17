module

public import TimeTraps.Spectral.RobinState
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

variable {n : ℕ} {P : RobinProblem n} {ev : ℝ}

def PositiveRobinEigenstate.gapValue (E : PositiveRobinEigenstate P ev) : Fin (n + 1) → ℝ → ℝ :=
  P.geometry.gapRestriction E.state

noncomputable def PositiveRobinEigenstate.logSlope (E : PositiveRobinEigenstate P ev)
    (e : Fin (n + 1)) (x : ℝ) : ℝ := E.slope e x / E.gapValue e x

theorem PositiveRobinEigenstate.gap_energy (E : PositiveRobinEigenstate P ev) (e : Fin (n + 1)) :
    IntervalEnergy (E.gapValue e) 0 (P.shooting.gap e) :=
  (P.geometry.restrict_energy E.energy).edge_energy e

theorem PositiveRobinEigenstate.gap_positive (E : PositiveRobinEigenstate P ev) (e : Fin (n + 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (P.shooting.gap e)) : 0 < E.gapValue e x :=
  E.positive _ (P.geometry.gap_point_mem e hx)

theorem PositiveRobinEigenstate.gap_continuous (E : PositiveRobinEigenstate P ev) (e : Fin (n + 1)) :
    ContinuousOn (E.gapValue e) (Icc (0 : ℝ) (P.shooting.gap e)) := by
  simpa only [uIcc_of_le (P.shooting.gap_pos e).le] using (E.gap_energy e).continuousOn

theorem PositiveRobinEigenstate.gap_left (E : PositiveRobinEigenstate P ev) (e : Fin (n + 1)) :
    E.gapValue e 0 = E.state (P.geometry.node e.castSucc) := by
  simp [gapValue, OrderedMedium.gapRestriction]

theorem PositiveRobinEigenstate.gap_right (E : PositiveRobinEigenstate P ev) (e : Fin (n + 1)) :
    E.gapValue e (P.shooting.gap e) = E.state (P.geometry.node e.succ) := by
  change E.state (P.geometry.node e.castSucc + (P.geometry.node e.succ - P.geometry.node e.castSucc)) = _
  rw [add_sub_cancel]

theorem PositiveRobinEigenstate.gap_trap_left (E : PositiveRobinEigenstate P ev) (i : Fin n) :
    E.gapValue i.castSucc (P.shooting.gap i.castSucc) = E.state (P.site i) := by
  rw [E.gap_right]
  change E.state (P.geometry.site i) = _
  rw [P.geometry_site]

theorem PositiveRobinEigenstate.gap_trap_right (E : PositiveRobinEigenstate P ev) (i : Fin n) :
    E.gapValue i.succ 0 = E.state (P.site i) := by
  rw [E.gap_left]
  change E.state (P.geometry.site i) = _
  rw [P.geometry_site]

theorem PositiveRobinEigenstate.logSlope_continuous (E : PositiveRobinEigenstate P ev) (e : Fin (n + 1)) :
    ContinuousOn (E.logSlope e) (Icc (0 : ℝ) (P.shooting.gap e)) :=
  (E.slope_continuous e).div (E.gap_continuous e) (fun _ hx => ne_of_gt (E.gap_positive e hx))

theorem PositiveRobinEigenstate.logSlope_hasDerivAt (E : PositiveRobinEigenstate P ev) (e : Fin (n + 1))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (P.shooting.gap e)) :
    HasDerivAt (E.logSlope e) (-ev / P.diffusivity - E.logSlope e x ^ 2) x := by
  have h := logarithmic_derivative (ne_of_gt (E.gap_positive e (Ioo_subset_Icc_self hx)))
    (E.state_derivative e x hx) (E.slope_derivative e x hx)
  unfold logSlope
  simpa only [neg_div] using h

theorem PositiveRobinEigenstate.logSlope_left (E : PositiveRobinEigenstate P ev) :
    E.logSlope 0 0 = P.betaLeft / P.diffusivity := by
  unfold logSlope
  rw [E.gap_left]
  change E.slope 0 0 / E.state (P.geometry.node 0) = P.betaLeft / P.diffusivity
  rw [P.geometry.node_first, P.geometry_left]
  have hu : E.state 0 ≠ 0 := ne_of_gt (E.positive 0 ⟨le_rfl, P.length_pos.le⟩)
  field_simp [hu, ne_of_gt P.diffusivity_pos]
  nlinarith [E.left_robin]

theorem PositiveRobinEigenstate.logSlope_right (E : PositiveRobinEigenstate P ev) :
    E.logSlope (Fin.last n) (P.shooting.gap (Fin.last n)) = -P.betaRight / P.diffusivity := by
  unfold logSlope
  rw [E.gap_right]
  change E.slope (Fin.last n) (P.shooting.gap (Fin.last n)) /
    E.state (P.geometry.node (Fin.last (n + 1))) = -P.betaRight / P.diffusivity
  rw [P.geometry.node_last, P.geometry_right]
  have hu : E.state P.length ≠ 0 := ne_of_gt (E.positive P.length ⟨P.length_pos.le, le_rfl⟩)
  field_simp [hu, ne_of_gt P.diffusivity_pos]
  nlinarith [E.right_robin]

theorem PositiveRobinEigenstate.logSlope_jump (E : PositiveRobinEigenstate P ev) (i : Fin n) :
    P.diffusivity * (E.logSlope i.succ 0 - E.logSlope i.castSucc (P.shooting.gap i.castSucc)) = P.strength i := by
  have hp : E.state (P.site i) ≠ 0 := ne_of_gt (E.positive _ (Ioo_subset_Icc_self (P.site_interior i)))
  have hj := E.reaction_jump i
  unfold logSlope
  rw [E.gap_trap_left, E.gap_trap_right]
  field_simp [hp]
  nlinarith

noncomputable def PositiveRobinEigenstate.gapRemainder (E : PositiveRobinEigenstate P ev)
    (v : ℝ → ℝ) (e : Fin (n + 1)) : ℝ :=
  ∫ x in (0 : ℝ)..P.shooting.gap e,
    (deriv (P.geometry.gapRestriction v e) x - E.logSlope e x * P.geometry.gapRestriction v e x) ^ 2

theorem PositiveRobinEigenstate.gapRemainder_nonneg (E : PositiveRobinEigenstate P ev) (v : ℝ → ℝ)
    (e : Fin (n + 1)) : 0 ≤ E.gapRemainder v e :=
  intervalIntegral.integral_nonneg (P.shooting.gap_pos e).le (fun _ _ => sq_nonneg _)

theorem PositiveRobinEigenstate.gap_square_identity (E : PositiveRobinEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) (e : Fin (n + 1)) :
    (∫ x in (0 : ℝ)..P.shooting.gap e, deriv (P.geometry.gapRestriction v e) x ^ 2) -
      ev / P.diffusivity * (∫ x in (0 : ℝ)..P.shooting.gap e, P.geometry.gapRestriction v e x ^ 2) =
      E.gapRemainder v e + E.logSlope e (P.shooting.gap e) * v (P.geometry.node e.succ) ^ 2 -
        E.logSlope e 0 * v (P.geometry.node e.castSucc) ^ 2 := by
  have h := riccati_square_identity (a := ev / P.diffusivity) (P.shooting.gap_pos e).le
    ((P.geometry.restrict_energy hv).edge_energy e) (E.logSlope_continuous e)
    (fun x hx => by simpa only [neg_div] using E.logSlope_hasDerivAt e hx)
  simpa only [gapRemainder, OrderedMedium.gapRestriction, add_zero, RobinProblem.shooting_gap,
    add_sub_cancel] using h

end TimeTraps.Spectral
