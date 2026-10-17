module

public import TimeTraps.Spectral.EigenstateCalculus

@[expose] public section

/-!
The full physical ground-state identity. Gap boundary terms cancel exactly
against the original point-interaction quadratic form. The remaining term
is a finite sum of nonnegative integrals for arbitrary H1 test functions.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ}

theorem SpectralProblem.gap_square_integral_sum (P : SpectralProblem n) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) :
    (∑ e, ∫ x in (0 : ℝ)..P.shooting.gap e, P.geometry.gapRestriction v e x ^ 2) = P.squareMass v :=
  P.geometry.integral_gap_sum hv.state_square_integrable

theorem SpectralProblem.gap_derivative_integral_sum (P : SpectralProblem n) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) :
    (∑ e, ∫ x in (0 : ℝ)..P.shooting.gap e, deriv (P.geometry.gapRestriction v e) x ^ 2) =
      ∫ x in (0 : ℝ)..P.length, deriv v x ^ 2 := by
  simp_rw [P.geometry.gapRestriction_deriv]
  exact P.geometry.integral_gap_sum hv.derivative_square_integrable

theorem PositiveEigenstate.boundary_cancellation (E : PositiveEigenstate P ev) (v : ℝ → ℝ) :
    P.diffusivity * (∑ e, (E.logSlope e (P.shooting.gap e) * v (P.geometry.node e.succ) ^ 2 -
      E.logSlope e 0 * v (P.geometry.node e.castSucc) ^ 2)) =
      -(∑ i, P.strength i * v (P.site i) ^ 2) := by
  let R := fun e : Fin (n + 1) => E.logSlope e (P.shooting.gap e) * v (P.geometry.node e.succ) ^ 2
  let A := fun e : Fin (n + 1) => E.logSlope e 0 * v (P.geometry.node e.castSucc) ^ 2
  have hR : R (Fin.last n) = 0 := by dsimp [R]; rw [E.logSlope_right, zero_mul]
  have hA : A 0 = 0 := by dsimp [A]; rw [E.logSlope_left, zero_mul]
  have hr := Fin.sum_univ_castSucc R
  have ha := Fin.sum_univ_succ A
  change P.diffusivity * (∑ e, (R e - A e)) = _
  rw [Finset.sum_sub_distrib, hr, ha, hR, hA, add_zero, zero_add, ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hsite : P.geometry.node i.castSucc.succ = P.site i := P.geometry_site i
  have hri : R i.castSucc = E.logSlope i.castSucc (P.shooting.gap i.castSucc) * v (P.site i) ^ 2 := by
    dsimp [R]
    rw [hsite]
  have hai : A i.succ = E.logSlope i.succ 0 * v (P.site i) ^ 2 := by
    change E.logSlope i.succ 0 * v (P.geometry.node i.castSucc.succ) ^ 2 = _
    rw [hsite]
  rw [hri, hai]
  calc
    _ = -(P.diffusivity * (E.logSlope i.succ 0 - E.logSlope i.castSucc (P.shooting.gap i.castSucc))) *
        v (P.site i) ^ 2 := by ring
    _ = _ := by rw [E.logSlope_jump]; ring

theorem PositiveEigenstate.ground_state_identity (E : PositiveEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) :
    P.quadraticForm v - ev * P.squareMass v = P.diffusivity * ∑ e, E.gapRemainder v e := by
  have hs : (∑ e, ((∫ x in (0 : ℝ)..P.shooting.gap e, deriv (P.geometry.gapRestriction v e) x ^ 2) -
      ev / P.diffusivity * (∫ x in (0 : ℝ)..P.shooting.gap e, P.geometry.gapRestriction v e x ^ 2))) =
      ∑ e, (E.gapRemainder v e + E.logSlope e (P.shooting.gap e) * v (P.geometry.node e.succ) ^ 2 -
        E.logSlope e 0 * v (P.geometry.node e.castSucc) ^ 2) :=
    Finset.sum_congr rfl (fun e _ => E.gap_square_identity hv e)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [P.gap_derivative_integral_sum hv, P.gap_square_integral_sum hv] at hs
  have hb := E.boundary_cancellation v
  rw [Finset.sum_sub_distrib] at hb
  calc
    P.quadraticForm v - ev * P.squareMass v =
        P.diffusivity * ((∫ x in (0 : ℝ)..P.length, deriv v x ^ 2) - ev / P.diffusivity * P.squareMass v) +
          ∑ i, P.strength i * v (P.site i) ^ 2 := by
      unfold SpectralProblem.quadraticForm
      field_simp [ne_of_gt P.diffusivity_pos]
      ring
    _ = P.diffusivity * ((∑ e, E.gapRemainder v e) +
        (∑ e, E.logSlope e (P.shooting.gap e) * v (P.geometry.node e.succ) ^ 2) -
        (∑ e, E.logSlope e 0 * v (P.geometry.node e.castSucc) ^ 2)) +
          ∑ i, P.strength i * v (P.site i) ^ 2 := by rw [hs]
    _ = P.diffusivity * (∑ e, E.gapRemainder v e) +
        (P.diffusivity * ((∑ e, E.logSlope e (P.shooting.gap e) * v (P.geometry.node e.succ) ^ 2) -
          (∑ e, E.logSlope e 0 * v (P.geometry.node e.castSucc) ^ 2)) +
          ∑ i, P.strength i * v (P.site i) ^ 2) := by ring
    _ = _ := by rw [hb]; ring

theorem PositiveEigenstate.quadraticForm_lower (E : PositiveEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) : ev * P.squareMass v ≤ P.quadraticForm v := by
  have h := E.ground_state_identity hv
  have hn : 0 ≤ P.diffusivity * ∑ e, E.gapRemainder v e :=
    mul_nonneg P.diffusivity_pos.le (Finset.sum_nonneg (fun e _ => E.gapRemainder_nonneg v e))
  linarith

end TimeTraps.Spectral
