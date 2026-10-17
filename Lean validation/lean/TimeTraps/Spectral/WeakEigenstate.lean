module

public import TimeTraps.Spectral.Rayleigh

@[expose] public section

/-!
Positive strong eigenstates satisfy the independent physical weak eigenvalue
equation against every H1 test function. The principal Rayleigh value has a
positive normalized representative satisfying that original equation.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ}

structure WeakEigenEquation (P : SpectralProblem n) (ev : ℝ) (u : ℝ → ℝ) : Prop where
  energy : IntervalEnergy u 0 P.length
  weak_form : ∀ v : ℝ → ℝ, IntervalEnergy v 0 P.length →
    P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv u x * deriv v x) +
      (∑ i, P.strength i * u (P.site i) * v (P.site i)) =
      ev * (∫ x in (0 : ℝ)..P.length, u x * v x)

theorem sum_gap_boundary (A B : Fin (n + 1) → ℝ) :
    (∑ e, (B e - A e)) = B (Fin.last n) - A 0 + ∑ i : Fin n, (B i.castSucc - A i.succ) := by
  have hb := Fin.sum_univ_castSucc B
  have ha := Fin.sum_univ_succ A
  rw [Finset.sum_sub_distrib, hb, ha, Finset.sum_sub_distrib]
  ring

theorem PositiveEigenstate.edge_equation (E : PositiveEigenstate P ev) (e : Fin (n + 1)) :
    EdgeEquation (fun _ => P.diffusivity) (fun x => ev * E.gapValue e x) 0 (P.shooting.gap e)
      (E.gapValue e) (fun x => P.diffusivity * E.slope e x) := by
  refine ⟨E.gap_continuous e, continuousOn_const.mul (E.slope_continuous e), ?_, ?_⟩
  · intro x hx
    rw [mul_div_cancel_left₀ _ (ne_of_gt P.diffusivity_pos)]
    exact E.state_derivative e x hx
  · intro x hx
    have h := (E.slope_derivative e x hx).const_mul P.diffusivity
    have he : P.diffusivity * (-(ev / P.diffusivity) * E.gapValue e x) = -(ev * E.gapValue e x) := by
      field_simp [ne_of_gt P.diffusivity_pos]
    change HasDerivAt (fun t => P.diffusivity * E.slope e t)
      (P.diffusivity * (-(ev / P.diffusivity) * E.gapValue e x)) x at h
    rwa [he] at h

theorem PositiveEigenstate.flux_boundary_cancellation (E : PositiveEigenstate P ev) (v : ℝ → ℝ) :
    (∑ e, (P.diffusivity * E.slope e (P.shooting.gap e) * v (P.geometry.node e.succ) -
      P.diffusivity * E.slope e 0 * v (P.geometry.node e.castSucc))) =
      -(∑ i, P.strength i * E.state (P.site i) * v (P.site i)) := by
  rw [sum_gap_boundary]
  simp only [E.left_reflecting, E.right_reflecting, mul_zero, zero_mul, sub_self, zero_add]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hsite : P.geometry.node i.castSucc.succ = P.site i := P.geometry_site i
  change P.diffusivity * E.slope i.castSucc (P.shooting.gap i.castSucc) * v (P.geometry.node i.castSucc.succ) -
    P.diffusivity * E.slope i.succ 0 * v (P.geometry.node i.castSucc.succ) = _
  rw [hsite]
  calc
    _ = -(P.diffusivity * (E.slope i.succ 0 - E.slope i.castSucc (P.shooting.gap i.castSucc))) * v (P.site i) := by ring
    _ = _ := by rw [E.reaction_jump]; ring

theorem PositiveEigenstate.to_weak (E : PositiveEigenstate P ev) : WeakEigenEquation P ev E.state := by
  refine ⟨E.energy, ?_⟩
  intro v hv
  have hlocal (e : Fin (n + 1)) := (E.edge_equation e).green_identity_energy
    (P.shooting.gap_pos e).le (continuousOn_const.mul (E.gap_continuous e))
    (fun _ _ => ne_of_gt P.diffusivity_pos) ((P.geometry.restrict_energy hv).edge_energy e)
  have hleft : (∑ e, ∫ x in (0 : ℝ)..P.shooting.gap e,
      P.diffusivity * deriv (E.gapValue e) x * deriv (P.geometry.gapRestriction v e) x) =
      P.diffusivity * (∫ x in (0 : ℝ)..P.length, deriv E.state x * deriv v x) := by
    simp_rw [gapValue, P.geometry.gapRestriction_deriv]
    change (∑ e, ∫ x in (0 : ℝ)..P.geometry.gapLength e,
      P.diffusivity * deriv E.state (P.geometry.node e.castSucc + x) * deriv v (P.geometry.node e.castSucc + x)) = _
    rw [P.geometry.integral_gap_sum (E.energy.bilinear_integrable hv continuousOn_const)]
    rw [P.geometry_left, P.geometry_right]
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
  have hright : (∑ e, ∫ x in (0 : ℝ)..P.shooting.gap e,
      ev * E.gapValue e x * P.geometry.gapRestriction v e x) =
      ev * (∫ x in (0 : ℝ)..P.length, E.state x * v x) := by
    have hconst : ContinuousOn (fun _ : ℝ => ev) (uIcc (0 : ℝ) P.length) := continuousOn_const
    have hc := (hconst.mul E.energy.continuousOn).mul hv.continuousOn
    change ContinuousOn (fun x => ev * E.state x * v x) (uIcc (0 : ℝ) P.length) at hc
    change (∑ e, ∫ x in (0 : ℝ)..P.geometry.gapLength e,
      ev * E.state (P.geometry.node e.castSucc + x) * v (P.geometry.node e.castSucc + x)) = _
    rw [P.geometry.integral_gap_sum hc.intervalIntegrable]
    rw [P.geometry_left, P.geometry_right]
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun e _ => hlocal e)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hs
  simp only [OrderedMedium.gapRestriction, SpectralProblem.shooting_gap, add_sub_cancel, add_zero] at hs
  change (∑ e, ∫ x in (0 : ℝ)..P.shooting.gap e,
    P.diffusivity * deriv (E.gapValue e) x * deriv (P.geometry.gapRestriction v e) x) =
    (∑ e, ∫ x in (0 : ℝ)..P.shooting.gap e, ev * E.gapValue e x * P.geometry.gapRestriction v e x) +
      (∑ e, P.diffusivity * E.slope e (P.shooting.gap e) * v (P.geometry.node e.succ)) -
      (∑ e, P.diffusivity * E.slope e 0 * v (P.geometry.node e.castSucc)) at hs
  rw [hleft, hright] at hs
  have hb := E.flux_boundary_cancellation v
  rw [Finset.sum_sub_distrib] at hb
  linarith

theorem SpectralProblem.positive_weak_principal_state_exists (P : SpectralProblem n) :
    ∃ u : ℝ → ℝ, WeakEigenEquation P P.principalValue u ∧
      (∀ x ∈ Icc (0 : ℝ) P.length, 0 < u x) ∧ u 0 = 1 := by
  obtain ⟨E, hE⟩ := P.principal_eigenstate_exists
  exact ⟨E.state, E.to_weak, E.positive, hE⟩

end TimeTraps.Spectral
