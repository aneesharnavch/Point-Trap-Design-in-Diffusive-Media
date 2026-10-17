module

public import TimeTraps.Spectral.RobinProblem
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

/-!
The physical endpoint penalties control the actual boundary traces. A
uniform bound on the quadratic forms forces the traces to zero when the
corresponding Robin coefficients tend to infinity. Merely asserting that
each form is finite would not give the uniform estimate needed for a limit.
-/

namespace TimeTraps.Spectral

open Filter Topology

variable {n : ℕ}

theorem RobinProblem.left_penalty_le_quadraticForm (P : RobinProblem n) (v : ℝ → ℝ) :
    P.betaLeft * v 0 ^ 2 ≤ P.quadraticForm v := by
  have hq := P.toSpectralProblem.quadraticForm_nonneg v
  have hr := mul_nonneg P.betaRight_nonneg (sq_nonneg (v P.length))
  unfold quadraticForm
  linarith

theorem RobinProblem.right_penalty_le_quadraticForm (P : RobinProblem n) (v : ℝ → ℝ) :
    P.betaRight * v P.length ^ 2 ≤ P.quadraticForm v := by
  have hq := P.toSpectralProblem.quadraticForm_nonneg v
  have hl := mul_nonneg P.betaLeft_nonneg (sq_nonneg (v 0))
  unfold quadraticForm
  linarith

theorem RobinProblem.left_trace_sq_le (P : RobinProblem n) (v : ℝ → ℝ)
    (hbeta : 0 < P.betaLeft) : v 0 ^ 2 ≤ P.quadraticForm v / P.betaLeft := by
  apply (le_div_iff₀ hbeta).mpr
  simpa only [mul_comm] using P.left_penalty_le_quadraticForm v

theorem RobinProblem.right_trace_sq_le (P : RobinProblem n) (v : ℝ → ℝ)
    (hbeta : 0 < P.betaRight) : v P.length ^ 2 ≤ P.quadraticForm v / P.betaRight := by
  apply (le_div_iff₀ hbeta).mpr
  simpa only [mul_comm] using P.right_penalty_le_quadraticForm v

theorem robin_trace_tendsto_zero_of_penalty_bound {ι : Type*} {l : Filter ι}
    {beta u : ι → ℝ} {C : ℝ} (hbeta : Tendsto beta l atTop)
    (hbound : ∀ᶠ i in l, beta i * u i ^ 2 ≤ C) : Tendsto u l (𝓝 0) := by
  have hsq : Tendsto (fun i => u i ^ 2) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun i => sq_nonneg (u i))) ?_
      ((tendsto_const_nhds : Tendsto (fun _ : ι => C) l (𝓝 C)).div_atTop hbeta)
    filter_upwards [hbeta.eventually (eventually_gt_atTop (0 : ℝ)), hbound] with i hi hb
    exact (le_div_iff₀ hi).mpr (by simpa only [mul_comm] using hb)
  apply (tendsto_zero_iff_abs_tendsto_zero u).mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsq.sqrt

theorem RobinProblem.left_trace_tendsto_zero_of_bounded_form {ι : Type*} {l : Filter ι}
    (P : ι → RobinProblem n) (v : ι → ℝ → ℝ) {C : ℝ}
    (hbeta : Tendsto (fun i => (P i).betaLeft) l atTop)
    (hbound : ∀ᶠ i in l, (P i).quadraticForm (v i) ≤ C) :
    Tendsto (fun i => v i 0) l (𝓝 0) := by
  apply robin_trace_tendsto_zero_of_penalty_bound hbeta
  exact hbound.mono (fun i hi => ((P i).left_penalty_le_quadraticForm (v i)).trans hi)

theorem RobinProblem.right_trace_tendsto_zero_of_bounded_form {ι : Type*} {l : Filter ι}
    (P : ι → RobinProblem n) (v : ι → ℝ → ℝ) {C : ℝ}
    (hbeta : Tendsto (fun i => (P i).betaRight) l atTop)
    (hbound : ∀ᶠ i in l, (P i).quadraticForm (v i) ≤ C) :
    Tendsto (fun i => v i ((P i).length)) l (𝓝 0) := by
  apply robin_trace_tendsto_zero_of_penalty_bound hbeta
  exact hbound.mono (fun i hi => ((P i).right_penalty_le_quadraticForm (v i)).trans hi)

end TimeTraps.Spectral
