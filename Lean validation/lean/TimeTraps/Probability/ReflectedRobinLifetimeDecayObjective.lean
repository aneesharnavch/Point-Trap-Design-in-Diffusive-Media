module

public import TimeTraps.Probability.ReflectedRobinLifetimeSpectralRate

@[expose] public section

/-! The decay objective is defined directly from the literal lifetime
survival probabilities. Its convergence and equality with the independent
Rayleigh value are theorems, not part of the objective's definition. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

noncomputable def reflectedRobinLifetimeDecayRate (P : RobinProblem n) (x : ℝ) : ℝ :=
  limUnder atTop (fun T : ℝ≥0 =>
    -Real.log (reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) / T.val)

theorem reflectedRobinLifetimeDecayRate_eq (P : RobinProblem n) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    reflectedRobinLifetimeDecayRate P x = P.principalValue :=
  (reflectedRobinPrincipal_lifetime_survival_log_rate P hx).limUnder_eq

theorem reflectedRobinLifetimeDecayRate_independent_start (P : RobinProblem n)
    {x y : ℝ} (hx : x ∈ Icc 0 P.length) (hy : y ∈ Icc 0 P.length) :
    reflectedRobinLifetimeDecayRate P x = reflectedRobinLifetimeDecayRate P y := by
  rw [reflectedRobinLifetimeDecayRate_eq P hx, reflectedRobinLifetimeDecayRate_eq P hy]

theorem reflectedRobinLifetimeDecayRate_pos (P : RobinProblem n) {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    0 < reflectedRobinLifetimeDecayRate P x := by
  rw [reflectedRobinLifetimeDecayRate_eq P hx]
  exact P.principalValue_pos

end TimeTraps.Probability
