module

public import TimeTraps.Analysis.PositiveQuotient
public import TimeTraps.Spectral.RobinQuotient
public import TimeTraps.Spectral.RobinWeak

@[expose] public section

/-! Ground-state equality and uniqueness on the physical Robin interval,
including all signed H1 minimizers and weak principal eigenfunctions. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

variable {n : ℕ} {P : RobinProblem n} {ev : ℝ}

theorem RobinWeakEigenEquation.self_quadraticForm {u : ℝ → ℝ}
    (h : RobinWeakEigenEquation P ev u) :
    P.quadraticForm u = ev * P.squareMass u := by
  simpa only [RobinProblem.quadraticForm, RobinProblem.squareMass,
    SpectralProblem.quadraticForm, SpectralProblem.squareMass,
    pow_two, mul_assoc] using h.weak_form u h.energy

theorem PositiveRobinEigenstate.proportional_of_quadraticForm_eq
    (E : PositiveRobinEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length)
    (he : P.quadraticForm v = ev * P.squareMass v) :
    EqOn v (fun x => (v 0 / E.state 0) * E.state x) (Icc 0 P.length) := by
  have hpos : ∀ x ∈ uIcc (0 : ℝ) P.length, 0 < E.state x := by
    intro x hx
    exact E.positive x (by simpa only [uIcc_of_le P.length_pos.le] using hx)
  have hq := interval_absolutelyContinuous_div hv.absolutelyContinuous
    E.energy.absolutelyContinuous hpos
  have hi := E.quotientSquare_integrable hv
  change IntervalIntegrable
    (fun x => E.state x ^ 2 * deriv (fun t => v t / E.state t) x ^ 2)
    volume 0 P.length at hi
  have hid := E.quotient_integral_identity hv
  rw [he, sub_self] at hid
  have hz : (∫ x in (0 : ℝ)..P.length,
      E.state x ^ 2 * deriv (fun t => v t / E.state t) x ^ 2) = 0 :=
    (mul_eq_zero.mp hid.symm).resolve_left (ne_of_gt P.diffusivity_pos)
  have hc := interval_absolutelyContinuous_constant_of_weighted_derivative_zero hq
    P.length_pos.le (fun x hx => sq_pos_of_pos (E.positive x hx)) hi hz
  intro x hx
  exact (div_eq_iff (ne_of_gt (E.positive x hx))).mp (hc x hx)

theorem PositiveRobinEigenstate.unique_scalar_of_quadraticForm_eq
    (E : PositiveRobinEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length)
    (he : P.quadraticForm v = ev * P.squareMass v) :
    ∃! c : ℝ, EqOn v (fun x => c * E.state x) (Icc 0 P.length) := by
  refine ⟨v 0 / E.state 0, E.proportional_of_quadraticForm_eq hv he, ?_⟩
  intro c hc
  apply (eq_div_iff (ne_of_gt (E.positive 0 ⟨le_rfl, P.length_pos.le⟩))).mpr
  exact (hc ⟨le_rfl, P.length_pos.le⟩).symm

theorem PositiveRobinEigenstate.squareMass_of_eq_scalar (E : PositiveRobinEigenstate P ev)
    {v : ℝ → ℝ} {c : ℝ}
    (h : EqOn v (fun x => c * E.state x) (Icc 0 P.length)) :
    P.squareMass v = c ^ 2 * P.squareMass E.state := by
  unfold RobinProblem.squareMass SpectralProblem.squareMass
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  change v x ^ 2 = c ^ 2 * E.state x ^ 2
  rw [h (x := x) (by simpa only [uIcc_of_le P.length_pos.le] using hx), mul_pow]

theorem PositiveRobinEigenstate.unique_nonzero_scalar_of_quadraticForm_eq
    (E : PositiveRobinEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) (hm : 0 < P.squareMass v)
    (he : P.quadraticForm v = ev * P.squareMass v) :
    ∃! c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * E.state x) (Icc 0 P.length) := by
  obtain ⟨c, hc, huniq⟩ := E.unique_scalar_of_quadraticForm_eq hv he
  have hcn : c ≠ 0 := by
    intro hz
    have hmass := E.squareMass_of_eq_scalar hc
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hmass
    exact (ne_of_gt hm) hmass
  exact ⟨c, ⟨hcn, hc⟩, fun d hd => huniq d hd.2⟩

theorem PositiveRobinEigenstate.rayleigh_minimizer_unique_scalar
    (E : PositiveRobinEigenstate P ev) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 P.length) (hm : 0 < P.squareMass v)
    (hmin : P.quadraticForm v / P.squareMass v = P.principalValue) :
    ∃! c : ℝ, c ≠ 0 ∧ EqOn v (fun x => c * E.state x) (Icc 0 P.length) := by
  apply E.unique_nonzero_scalar_of_quadraticForm_eq hv hm
  exact (div_eq_iff (ne_of_gt hm)).mp (hmin.trans E.principalValue_eq)

theorem PositiveRobinEigenstate.weak_state_unique_scalar (E : PositiveRobinEigenstate P ev)
    {v : ℝ → ℝ} (hv : RobinWeakEigenEquation P ev v) :
    ∃! c : ℝ, EqOn v (fun x => c * E.state x) (Icc 0 P.length) :=
  E.unique_scalar_of_quadraticForm_eq hv.energy hv.self_quadraticForm

theorem RobinWeakEigenEquation.eqOn_of_initial_value {u v : ℝ → ℝ}
    (hu : RobinWeakEigenEquation P P.principalValue u)
    (hv : RobinWeakEigenEquation P P.principalValue v) (h0 : u 0 = v 0) :
    EqOn u v (Icc 0 P.length) := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  have heu := E.proportional_of_quadraticForm_eq hu.energy hu.self_quadraticForm
  have hev := E.proportional_of_quadraticForm_eq hv.energy hv.self_quadraticForm
  intro x hx
  rw [heu hx, hev hx, h0]

theorem RobinProblem.normalized_principal_weak_state_unique (P : RobinProblem n) :
    ∃ u : ℝ → ℝ, RobinWeakEigenEquation P P.principalValue u ∧ u 0 = 1 ∧
      ∀ v : ℝ → ℝ, RobinWeakEigenEquation P P.principalValue v → v 0 = 1 →
        EqOn v u (Icc 0 P.length) := by
  obtain ⟨E, hE0⟩ := P.principal_eigenstate_exists
  refine ⟨E.state, E.to_weak, hE0, ?_⟩
  intro v hv hv0
  exact hv.eqOn_of_initial_value E.to_weak (hv0.trans hE0.symm)

theorem PositiveRobinEigenstate.state_eqOn_of_initial_value (E : PositiveRobinEigenstate P ev)
    {r : ℝ} (F : PositiveRobinEigenstate P r) (h0 : E.state 0 = F.state 0) :
    EqOn E.state F.state (Icc 0 P.length) := by
  have he : RobinWeakEigenEquation P P.principalValue E.state := by
    rw [E.principalValue_eq]
    exact E.to_weak
  have hf : RobinWeakEigenEquation P P.principalValue F.state := by
    rw [F.principalValue_eq]
    exact F.to_weak
  exact he.eqOn_of_initial_value hf h0

theorem RobinWeakEigenEquation.positive_of_initial_value_pos {u : ℝ → ℝ}
    (hu : RobinWeakEigenEquation P P.principalValue u) (h0 : 0 < u 0) :
    ∀ x ∈ Icc 0 P.length, 0 < u x := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  have he := E.proportional_of_quadraticForm_eq hu.energy hu.self_quadraticForm
  intro x hx
  rw [he hx]
  exact mul_pos (div_pos h0 (E.positive 0 ⟨le_rfl, P.length_pos.le⟩)) (E.positive x hx)

end TimeTraps.Spectral
