module

public import TimeTraps.Probability.ReflectedLifetimeSpectralRate

@[expose] public section

/-! The decay objective is defined directly from the literal lifetime
survival probabilities. Its convergence and equality with the independent
Rayleigh value are theorems, not part of the objective's definition. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

noncomputable def reflectedLifetimeDecayRate (P : SpectralProblem n) (x : ℝ) : ℝ :=
  limUnder atTop (fun T : ℝ≥0 =>
    -Real.log (reflectedAtomicSurvivalProbability P.length P.diffusivity x P.site P.strength T) / T.val)

theorem reflectedLifetimeDecayRate_eq (P : SpectralProblem n) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    reflectedLifetimeDecayRate P x = P.principalValue :=
  (reflectedPrincipal_lifetime_survival_log_rate P hx).limUnder_eq

theorem reflectedLifetimeDecayRate_independent_start (P : SpectralProblem n)
    {x y : ℝ} (hx : x ∈ Icc 0 P.length) (hy : y ∈ Icc 0 P.length) :
    reflectedLifetimeDecayRate P x = reflectedLifetimeDecayRate P y := by
  rw [reflectedLifetimeDecayRate_eq P hx, reflectedLifetimeDecayRate_eq P hy]

theorem reflectedLifetimeDecayRate_pos (P : SpectralProblem n) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    0 < reflectedLifetimeDecayRate P x := by
  rw [reflectedLifetimeDecayRate_eq P hx]
  exact P.principalValue_pos

end TimeTraps.Probability
