module

public import TimeTraps.Spectral.WeakEigenstate
public import TimeTraps.Spectral.PhaseJump

@[expose] public section

/-!
Principal phases of actual positive physical eigenstates. Positivity justifies
the logarithmic derivative, the Riccati equation gives constant phase speed,
and the original reflecting and reaction laws give the exact global phase sum.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev k : ℝ}

noncomputable def PositiveEigenstate.phase (E : PositiveEigenstate P ev)
    (k : ℝ) (e : Fin (n + 1)) (x : ℝ) : ℝ := Real.arctan (E.logSlope e x / k)

theorem PositiveEigenstate.phase_branch (E : PositiveEigenstate P ev)
    (k : ℝ) (e : Fin (n + 1)) (x : ℝ) :
    E.phase k e x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩

theorem PositiveEigenstate.phase_continuous (E : PositiveEigenstate P ev)
    (k : ℝ) (e : Fin (n + 1)) :
    ContinuousOn (E.phase k e) (Icc (0 : ℝ) (P.shooting.gap e)) :=
  Real.continuous_arctan.comp_continuousOn ((E.logSlope_continuous e).div_const k)

theorem PositiveEigenstate.phase_hasDerivAt (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (P.shooting.gap e)) :
    HasDerivAt (E.phase k e) (-k) x := by
  have h := ((E.logSlope_hasDerivAt e hx).div_const k).arctan
  have he : 1 / (1 + (E.logSlope e x / k) ^ 2) *
      ((-ev / P.diffusivity - E.logSlope e x ^ 2) / k) = -k := by
    rw [neg_div, ← hk2]
    field_simp [ne_of_gt hk]
    ring
  rwa [he] at h

theorem PositiveEigenstate.phase_affine (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (P.shooting.gap e)) :
    E.phase k e x = E.phase k e 0 - k * x := by
  have h := integral_derivative_to_point (E.phase_continuous k e)
    (show ContinuousOn (fun _ : ℝ => -k) (Icc (0 : ℝ) (P.shooting.gap e)) from continuousOn_const)
    (fun y hy => E.phase_hasDerivAt hk hk2 e hy) hx
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  linarith

theorem PositiveEigenstate.phase_left (E : PositiveEigenstate P ev) (k : ℝ) :
    E.phase k 0 0 = 0 := by simp [phase, E.logSlope_left]

theorem PositiveEigenstate.phase_right (E : PositiveEigenstate P ev) (k : ℝ) :
    E.phase k (Fin.last n) (P.shooting.gap (Fin.last n)) = 0 := by
  simp [phase, E.logSlope_right]

theorem PositiveEigenstate.phase_tan_jump (E : PositiveEigenstate P ev) (hk : 0 < k) (i : Fin n) :
    Real.tan (E.phase k i.succ 0) - Real.tan (E.phase k i.castSucc (P.shooting.gap i.castSucc)) =
      P.strength i / (P.diffusivity * k) := by
  simp only [phase, Real.tan_arctan]
  have h := E.logSlope_jump i
  field_simp [ne_of_gt hk, ne_of_gt P.diffusivity_pos]
  nlinarith

theorem PositiveEigenstate.phase_jump_sharp (E : PositiveEigenstate P ev) (hk : 0 < k) (i : Fin n) :
    E.phase k i.succ 0 - E.phase k i.castSucc (P.shooting.gap i.castSucc) ≤
      2 * Real.arctan (P.strength i / (2 * P.diffusivity * k)) ∧
    (E.phase k i.succ 0 - E.phase k i.castSucc (P.shooting.gap i.castSucc) =
      2 * Real.arctan (P.strength i / (2 * P.diffusivity * k)) ↔
      E.phase k i.succ 0 = -E.phase k i.castSucc (P.shooting.gap i.castSucc)) := by
  have h := sharp_phase_jump (div_pos (P.strength_pos i) (mul_pos P.diffusivity_pos hk))
    (E.phase_branch k i.castSucc (P.shooting.gap i.castSucc)) (E.phase_branch k i.succ 0)
    (E.phase_tan_jump hk i)
  have he : P.strength i / (P.diffusivity * k) / 2 = P.strength i / (2 * P.diffusivity * k) := by ring
  rwa [he] at h

theorem SpectralProblem.gap_sum (P : SpectralProblem n) : (∑ e, P.shooting.gap e) = P.length := by
  simp_rw [P.shooting_gap]
  rw [fin_sum_adjacent_difference, P.geometry.node_first, P.geometry.node_last,
    P.geometry_left, P.geometry_right, sub_zero]

theorem PositiveEigenstate.phase_sum (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    k * P.length = ∑ i : Fin n,
      (E.phase k i.succ 0 - E.phase k i.castSucc (P.shooting.gap i.castSucc)) := by
  have hs := sum_gap_boundary (fun e => E.phase k e 0) (fun e => E.phase k e (P.shooting.gap e))
  rw [E.phase_left, E.phase_right, sub_self, zero_add] at hs
  have hgap (e : Fin (n + 1)) :
      E.phase k e (P.shooting.gap e) - E.phase k e 0 = -k * P.shooting.gap e := by
    rw [E.phase_affine hk hk2 e ⟨(P.shooting.gap_pos e).le, le_rfl⟩]
    ring
  simp_rw [hgap] at hs
  rw [← Finset.mul_sum, P.gap_sum] at hs
  have hneg : (∑ i : Fin n, (E.phase k i.castSucc (P.shooting.gap i.castSucc) - E.phase k i.succ 0)) =
      -(∑ i : Fin n, (E.phase k i.succ 0 - E.phase k i.castSucc (P.shooting.gap i.castSucc))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hneg] at hs
  linarith

theorem PositiveEigenstate.phase_global_bound (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    P.length * k ≤ 2 * ∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k)) := by
  rw [mul_comm P.length, E.phase_sum hk hk2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (E.phase_jump_sharp hk i).1)

end TimeTraps.Spectral
