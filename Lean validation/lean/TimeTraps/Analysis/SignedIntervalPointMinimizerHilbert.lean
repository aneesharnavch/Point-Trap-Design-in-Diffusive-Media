module

public import TimeTraps.Analysis.SignedIntervalPointVariationalMinimum
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Euler--Lagrange follows from the Rayleigh lower bound on the entire
actual H1 space. Zero-mass perturbations remain covered by that bound;
no operator-domain or weak-eigenfunction premise is used. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.form_principal_lower
    (P : SignedIntervalPointProblem ι l r) (u : IntervalSobolevSpace l r) :
    P.principalValue * ‖u.state‖ ^ 2 ≤ P.form u u := by
  rw [P.principalValue_eq_first]
  exact P.form_first_lower u

theorem SignedIntervalPointProblem.minimizer_hilbert
    (P : SignedIntervalPointProblem ι l r) (u : IntervalSobolevSpace l r)
    (he : P.form u u = P.principalValue * ‖u.state‖ ^ 2) :
    ∀ v : IntervalSobolevSpace l r,
      P.form u v = P.principalValue * inner ℝ u.state v.state := by
  intro v
  let b := P.form u v - P.principalValue * inner ℝ u.state v.state
  let a := P.form v v - P.principalValue * ‖v.state‖ ^ 2
  have hsym : P.form v u = P.form u v :=
    intervalSobolevPointForm_symmetric P.interval_pos P.diffusivity P.strength P.site
      P.site_mem v u
  have hp (t : ℝ) : 0 ≤ 2 * t * b + t ^ 2 * a := by
    have h := P.form_principal_lower (u + t • v)
    have hs : (u + t • v).state = u.state + t • v.state := by
      change stateL l r (u + t • v) = stateL l r u + t • stateL l r v
      simp only [map_add, map_smul]
    rw [hs, ← real_inner_self_eq_norm_sq] at h
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
    rw [real_inner_comm u.state v.state, hsym, he] at h
    dsimp only [a, b]
    nlinarith
  have hmin : IsLocalMin (fun t : ℝ => 2 * t * b + t ^ 2 * a) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using hp t
  have hd : HasDerivAt (fun t : ℝ => 2 * t * b + t ^ 2 * a) (2 * b) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const b).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const a) using 1
    norm_num
  have hz := hmin.hasDerivAt_eq_zero hd
  dsimp only [b] at hz
  linarith

end TimeTraps.Analysis
