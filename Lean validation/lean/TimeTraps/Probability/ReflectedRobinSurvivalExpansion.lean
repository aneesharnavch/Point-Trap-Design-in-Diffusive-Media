module

public import TimeTraps.Probability.ReflectedRobinSurvivalGroundRemainder
public import TimeTraps.Probability.ReflectedLifetimeSpectralRate

@[expose] public section

/-! At every physical starting point, actual survival has a positive
first-mode coefficient and an explicit remainder bounded at the second
spectral rate. The bound holds for all times at least one, including
boundary starting points. The spectral gap is derived from the original
weak operator, not supplied as an assumption. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

noncomputable def reflectedRobinSurvivalRemainderConstant (P : RobinProblem n) (x : ℝ) : ℝ :=
  reflectedKilledPointConstant P.toSpectralProblem 1 zero_lt_one x * ‖reflectedRobinSurvivalGroundRemainder P‖ *
    Real.exp (P.intervalPointProblem.spectralEnumeration 1).1⁻¹

theorem reflectedRobinSurvivalRemainderConstant_nonneg (P : RobinProblem n) (x : ℝ) :
    0 ≤ reflectedRobinSurvivalRemainderConstant P x :=
  mul_nonneg (mul_nonneg (reflectedKilledPointConstant_nonneg P.toSpectralProblem 1 zero_lt_one x)
    (norm_nonneg _)) (Real.exp_pos _).le

theorem reflectedRobinAtomicMeanSurvival_expansion_bound (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) (T : ℝ≥0) (hT : 1 ≤ T) :
    |reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T -
      Real.exp (-P.principalValue * T.val) * reflectedRobinSurvivalFirstCoefficient P x| ≤
      reflectedRobinSurvivalRemainderConstant P x *
        Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val) := by
  have hb := reflectedRobinAtomicMeanSurvival_ground_remainder_shifted P 1 zero_lt_one (T - 1) x
  have ht : (1 : ℝ≥0) + (T - 1) = T := add_tsub_cancel_of_le hT
  rw [ht, reflectedFold_eq_self P.length P.length_pos x hx] at hb
  refine hb.trans_eq ?_
  have hc : (T - 1 : ℝ≥0).val = T.val - 1 := NNReal.coe_sub hT
  rw [hc]
  have he : -(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * (T.val - 1) =
      (P.intervalPointProblem.spectralEnumeration 1).1⁻¹ +
        -(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val := by ring
  rw [he, Real.exp_add]
  unfold reflectedRobinSurvivalRemainderConstant
  ring

theorem reflectedRobinAtomicSurvivalProbability_expansion_bound (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) (T : ℝ≥0) (hT : 1 ≤ T) :
    |reflectedAtomicSurvivalProbability P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T -
      Real.exp (-P.principalValue * T.val) * reflectedRobinSurvivalFirstCoefficient P x| ≤
      reflectedRobinSurvivalRemainderConstant P x *
        Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val) := by
  rw [reflectedAtomicSurvivalProbability_eq P.length P.length_pos P.diffusivity P.diffusivity_pos
    x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg)]
  exact reflectedRobinAtomicMeanSurvival_expansion_bound P hx T hT

theorem reflectedRobinAtomicSurvivalProbability_expansion (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) :
    0 < reflectedRobinSurvivalFirstCoefficient P x ∧
      P.principalValue < (P.intervalPointProblem.spectralEnumeration 1).1⁻¹ ∧
      Asymptotics.IsBigO atTop
        (fun T : ℝ≥0 => reflectedAtomicSurvivalProbability P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T -
          Real.exp (-P.principalValue * T.val) * reflectedRobinSurvivalFirstCoefficient P x)
        (fun T : ℝ≥0 => Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * T.val)) := by
  refine ⟨reflectedRobinSurvivalFirstCoefficient_pos P hx, ?_, ?_⟩
  · simpa only [P.interval_first_eigenvalue] using P.interval_first_lt_second_eigenvalue
  · apply Asymptotics.IsBigO.of_bound (reflectedRobinSurvivalRemainderConstant P x)
    filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with T hT
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      reflectedRobinAtomicSurvivalProbability_expansion_bound P hx T hT

end TimeTraps.Probability
