module

public import TimeTraps.Analysis.SignedPeriodicPointVariationalMinimum
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Euler--Lagrange follows from the Rayleigh lower bound on the full
endpoint-matched periodic H1 space. The perturbations preserve precisely the periodic
boundary traces. No weak-eigenstate or operator-domain premise is used. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter InnerProductSpace IntervalSobolevSpace
open scoped Topology

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.form_principal_lower
    (P : SignedPeriodicPointProblem ι l r) (u : IntervalPeriodicSpace P.boundary) :
    P.principalValue * ‖P.boundary.stateL u‖ ^ 2 ≤ P.form u u := by
  rw [P.principalValue_eq_first]
  exact P.form_first_lower u

theorem SignedPeriodicPointProblem.minimizer_hilbert
    (P : SignedPeriodicPointProblem ι l r) (u : IntervalPeriodicSpace P.boundary)
    (he : P.form u u = P.principalValue * ‖P.boundary.stateL u‖ ^ 2) :
    ∀ v : IntervalPeriodicSpace P.boundary,
      P.form u v = P.principalValue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v) := by
  intro v
  let b := P.form u v - P.principalValue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v)
  let a := P.form v v - P.principalValue * ‖P.boundary.stateL v‖ ^ 2
  have hsym : P.form v u = P.form u v :=
    intervalPeriodicPointForm_symmetric P.boundary P.diffusivity P.strength P.site
      P.site_mem v u
  have hp (t : ℝ) : 0 ≤ 2 * t * b + t ^ 2 * a := by
    have h := P.form_principal_lower (u + t • v)
    have hs : P.boundary.stateL (u + t • v) =
        P.boundary.stateL u + t • P.boundary.stateL v := by
      simp only [map_add, map_smul]
    rw [hs, ← real_inner_self_eq_norm_sq] at h
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h
    rw [real_inner_comm (P.boundary.stateL u) (P.boundary.stateL v), hsym, he] at h
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
