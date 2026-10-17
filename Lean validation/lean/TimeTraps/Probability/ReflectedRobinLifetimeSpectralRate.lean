module

public import TimeTraps.Probability.ReflectedRobinGroundSurvivalBounds
public import TimeTraps.Probability.ReflectedAttainmentSurvivalExpansion
public import TimeTraps.Analysis.ExponentialSurvivalRate

@[expose] public section

/-! The literal Robin first-attainment lifetime has the original full
Robin Rayleigh value as its logarithmic survival rate. Positive compact
ground bounds derive the limit at every physical start, including endpoints. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

theorem reflectedRobinPrincipal_lifetime_survival_bounds (P : RobinProblem n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ Icc 0 P.length, ∀ T : ℝ≥0,
      c * Real.exp (-P.principalValue * T.val) ≤
        reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ∧
      reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ≤
        C * Real.exp (-P.principalValue * T.val) := by
  obtain ⟨c, C, hc, hC, hb⟩ := reflectedRobinPrincipal_survival_uniform_bounds P
  refine ⟨c, C, hc, hC, ?_⟩
  intro x hx T
  rw [reflectedAtomicAttainmentSurvivalProbability_eq P.length P.length_pos P.diffusivity P.diffusivity_pos
    x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg),
    reflectedAtomicSurvivalProbability_eq P.length P.length_pos P.diffusivity P.diffusivity_pos
      x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight)
        (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg)]
  exact hb x hx T

theorem reflectedRobinPrincipal_mean_survival_log_rate (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Tendsto (fun T : ℝ≥0 =>
      -Real.log (reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) / T.val)
      atTop (𝓝 P.principalValue) := by
  obtain ⟨c, C, hc, hC, hb⟩ := reflectedRobinPrincipal_survival_uniform_bounds P
  exact exponentialSurvivalRate hc hC (hb x hx)

theorem reflectedRobinPrincipal_lifetime_survival_log_rate (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    Tendsto (fun T : ℝ≥0 =>
      -Real.log (reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T) / T.val)
      atTop (𝓝 P.principalValue) := by
  obtain ⟨c, C, hc, hC, hb⟩ := reflectedRobinPrincipal_lifetime_survival_bounds P
  exact exponentialSurvivalRate hc hC (hb x hx)

end TimeTraps.Probability
