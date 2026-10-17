module

public import TimeTraps.Spectral.RobinEndpointEnergy
public import TimeTraps.Spectral.RobinPrincipalBound
public import TimeTraps.Spectral.RobinUniqueness

@[expose] public section

/-!
For mass-normalized weak principal states, the uniform physical energy bound
needed for a Dirichlet trace limit follows from the phase bound itself.
The interior strengths and sites may vary; length, diffusivity and count
are fixed. No positivity of the competing weak states is required.
-/

namespace TimeTraps.Spectral

open Filter Topology

variable {n : ℕ}

theorem RobinWeakEigenEquation.normalized_form_lt_absorbing_bound
    {P : RobinProblem n} {u : ℝ → ℝ}
    (hu : RobinWeakEigenEquation P P.principalValue u) (hm : P.squareMass u = 1) :
    P.quadraticForm u < P.diffusivity * ((((n : ℝ) + 1) * Real.pi) / P.length) ^ 2 := by
  rw [hu.self_quadraticForm, hm, mul_one]
  exact P.principalValue_lt_absorbing_bound

theorem robin_principal_left_trace_tendsto_zero {ι : Type*} {l : Filter ι}
    (P : ι → RobinProblem n) (u : ι → ℝ → ℝ) {L D : ℝ}
    (hL : ∀ i, (P i).length = L) (hD : ∀ i, (P i).diffusivity = D)
    (hu : ∀ i, RobinWeakEigenEquation (P i) (P i).principalValue (u i))
    (hm : ∀ i, (P i).squareMass (u i) = 1)
    (hbeta : Tendsto (fun i => (P i).betaLeft) l atTop) :
    Tendsto (fun i => u i 0) l (𝓝 0) := by
  apply RobinProblem.left_trace_tendsto_zero_of_bounded_form P u hbeta
    (C := D * ((((n : ℝ) + 1) * Real.pi) / L) ^ 2)
  apply Eventually.of_forall
  intro i
  have h := (hu i).normalized_form_lt_absorbing_bound (hm i)
  rw [hL i, hD i] at h
  exact h.le

theorem robin_principal_right_trace_tendsto_zero {ι : Type*} {l : Filter ι}
    (P : ι → RobinProblem n) (u : ι → ℝ → ℝ) {L D : ℝ}
    (hL : ∀ i, (P i).length = L) (hD : ∀ i, (P i).diffusivity = D)
    (hu : ∀ i, RobinWeakEigenEquation (P i) (P i).principalValue (u i))
    (hm : ∀ i, (P i).squareMass (u i) = 1)
    (hbeta : Tendsto (fun i => (P i).betaRight) l atTop) :
    Tendsto (fun i => u i L) l (𝓝 0) := by
  have h := RobinProblem.right_trace_tendsto_zero_of_bounded_form P u hbeta
    (C := D * ((((n : ℝ) + 1) * Real.pi) / L) ^ 2) (by
      apply Eventually.of_forall
      intro i
      have hi := (hu i).normalized_form_lt_absorbing_bound (hm i)
      rw [hL i, hD i] at hi
      exact hi.le)
  simpa only [hL] using h

end TimeTraps.Spectral
