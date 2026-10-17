module

public import TimeTraps.Probability.ReflectedRobinSurvivalExpansion
public import TimeTraps.Probability.ReflectedAttainmentSurvivalExpansion
public import TimeTraps.Probability.ReflectedAtomicLifetimeConvention

@[expose] public section

/-! The every-start expansion applies to the paper's literal first
attainment of the independent exponential threshold. Equality of the
two lifetime conventions was proved almost surely as an extended value. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

theorem reflectedRobinAtomicAttainmentSurvivalProbability_expansion_bound (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) (T : ℝ≥0) (hT : 1 ≤ T) :
    |reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T -
      Real.exp (-P.principalValue * T.val) * reflectedRobinSurvivalFirstCoefficient P x| ≤
      reflectedRobinSurvivalRemainderConstant P x *
        Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val) := by
  rw [reflectedAtomicAttainmentSurvivalProbability_eq P.length P.length_pos P.diffusivity
    P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg)]
  exact reflectedRobinAtomicSurvivalProbability_expansion_bound P hx T hT

theorem reflectedRobinAtomicAttainmentSurvivalProbability_expansion (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    0 < reflectedRobinSurvivalFirstCoefficient P x ∧
      P.principalValue < (P.intervalPointProblem.spectralEnumeration 1).1⁻¹ ∧
      Asymptotics.IsBigO atTop
        (fun T : ℝ≥0 => reflectedAtomicAttainmentSurvivalProbability P.length P.diffusivity
          x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T - Real.exp (-P.principalValue * T.val) *
            reflectedRobinSurvivalFirstCoefficient P x)
        (fun T : ℝ≥0 => Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val)) := by
  have he (T : ℝ≥0) := reflectedAtomicAttainmentSurvivalProbability_eq P.length P.length_pos
    P.diffusivity P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg) T
  simp only [he]
  exact reflectedRobinAtomicSurvivalProbability_expansion P hx

end TimeTraps.Probability
