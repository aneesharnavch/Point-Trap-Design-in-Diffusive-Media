module

public import TimeTraps.Spectral.DirichletUniqueness
public import TimeTraps.Spectral.DirichletVariational

@[expose] public section

/-! Complete equality classification in the original signed H1 Rayleigh
problem. All minimizers are exactly the nonzero scalar multiples of the
explicit ground mode on the physical closed interval. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

theorem DirichletInterval.quadraticForm_of_eq_ground_scalar (P : DirichletInterval)
    {u : ℝ → ℝ} {c : ℝ} (h : EqOn u (fun x => c * P.groundState x) (Icc 0 P.length)) :
    P.quadraticForm u = c ^ 2 * P.quadraticForm P.groundState := by
  have hi : (∫ x in (0 : ℝ)..P.length, deriv u x ^ 2) =
      ∫ x in (0 : ℝ)..P.length, c ^ 2 * deriv P.groundState x ^ 2 := by
    apply intervalIntegral.integral_congr_Ioo_of_le P.length_pos.le
    intro x hx
    have hd : deriv P.groundState x = P.groundSlope x :=
      (dirichletCosine_hasDerivAt P.waveNumber P.center x).deriv
    have hdc := (dirichletCosine_hasDerivAt P.waveNumber P.center x).const_mul c
    change HasDerivAt (fun t => c * P.groundState t) (c * P.groundSlope x) x at hdc
    change deriv u x ^ 2 = c ^ 2 * deriv P.groundState x ^ 2
    rw [((h.mono Ioo_subset_Icc_self).deriv isOpen_Ioo) hx, hdc.deriv, hd, mul_pow]
  unfold quadraticForm
  rw [hi, intervalIntegral.integral_const_mul]
  ring

theorem DirichletInterval.quadraticForm_eq_iff_ground_scalar (P : DirichletInterval)
    {u : ℝ → ℝ} (hu : P.admissible u) :
    P.quadraticForm u = P.principalValue * P.squareMass u ↔
      ∃ c : ℝ, EqOn u (fun x => c * P.groundState x) (Icc 0 P.length) := by
  constructor
  · intro he
    exact (P.weak_of_quadraticForm_eq hu he).unique_scalar.exists
  · rintro ⟨c, hc⟩
    rw [P.quadraticForm_of_eq_ground_scalar hc, P.squareMass_of_eq_ground_scalar hc,
      P.principal_ground_state.self_quadraticForm]
    ring

theorem DirichletInterval.unique_scalar_of_quadraticForm_eq (P : DirichletInterval)
    {u : ℝ → ℝ} (hu : P.admissible u)
    (he : P.quadraticForm u = P.principalValue * P.squareMass u) :
    ∃! c : ℝ, EqOn u (fun x => c * P.groundState x) (Icc 0 P.length) :=
  (P.weak_of_quadraticForm_eq hu he).unique_scalar

theorem DirichletInterval.rayleigh_minimizer_unique_scalar (P : DirichletInterval)
    {u : ℝ → ℝ} (hu : P.admissible u) (hm : 0 < P.squareMass u)
    (he : P.quadraticForm u / P.squareMass u = P.principalValue) :
    ∃! c : ℝ, c ≠ 0 ∧ EqOn u (fun x => c * P.groundState x) (Icc 0 P.length) :=
  (P.weak_of_rayleigh_minimizer hu hm he).unique_nonzero_scalar hm

theorem DirichletInterval.rayleigh_minimizer_iff (P : DirichletInterval)
    {u : ℝ → ℝ} (hu : P.admissible u) :
    (0 < P.squareMass u ∧ P.quadraticForm u / P.squareMass u = P.principalValue) ↔
      ∃ c : ℝ, c ≠ 0 ∧ EqOn u (fun x => c * P.groundState x) (Icc 0 P.length) := by
  constructor
  · rintro ⟨hm, he⟩
    exact (P.rayleigh_minimizer_unique_scalar hu hm he).exists
  · rintro ⟨c, hc, he⟩
    have hm : 0 < P.squareMass u := by
      rw [P.squareMass_of_eq_ground_scalar he]
      exact mul_pos (sq_pos_of_ne_zero hc) P.groundState_mass_pos
    refine ⟨hm, (div_eq_iff hm.ne').mpr ?_⟩
    exact (P.quadraticForm_eq_iff_ground_scalar hu).mpr ⟨c, he⟩

end TimeTraps.Spectral
