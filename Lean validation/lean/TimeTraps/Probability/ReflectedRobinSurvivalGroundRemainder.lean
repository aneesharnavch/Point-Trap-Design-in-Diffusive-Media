module

public import TimeTraps.Probability.ReflectedRobinSurvivalFirstMode

@[expose] public section

/-! The second spectral rate controls the actual killed survival
remainder at every start after any fixed positive smoothing time.
Both the smoothing functional and the killed L² evolution were
constructed from the literal expectation before their identification. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

theorem reflectedRobinKilledInterval_survival_ground_remainder_le (P : RobinProblem n)
    (t : ℝ≥0) :
    ‖reflectedRobinKilledIntervalL2Operator P t (reflectedRobinSurvivalOne P) -
      (Real.exp (-P.principalValue * t.val) *
        inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
          (reflectedRobinSurvivalOne P)) •
        P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)‖ ≤
      Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * t.val) *
        ‖reflectedRobinSurvivalGroundRemainder P‖ := by
  rw [reflectedRobinKilledIntervalL2Operator_eq_heat]
  exact P.interval_heat_ground_remainder_le t (reflectedRobinSurvivalOne P)

theorem reflectedRobinKilledPointEvaluation_ground_remainder (P : RobinProblem n)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (x : ℝ) :
    reflectedRobinKilledPointEvaluation P s hs x
      (reflectedRobinKilledIntervalL2Operator P t (reflectedRobinSurvivalOne P) -
        (Real.exp (-P.principalValue * t.val) *
          inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
            (reflectedRobinSurvivalOne P)) •
          P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)) =
      reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) (s + t) -
        Real.exp (-P.principalValue * (s + t).val) *
          reflectedRobinSurvivalFirstCoefficient P (reflectedFold P.length x) := by
  have hQ := (reflectedRobinKilledPointEvaluation_add_apply P s hs t x
    (reflectedRobinSurvivalOne P)).symm.trans
      (reflectedRobinKilledPointEvaluation_survival P (s + t)
        (add_pos_of_pos_of_nonneg hs (show 0 ≤ t from zero_le)) x)
  have hphi := reflectedRobinKilledPointEvaluation_eigenbasis P s hs x
    (P.intervalPointProblem.spectralEnumeration 0)
  rw [P.interval_first_eigenvalue] at hphi
  have hcoef : Real.exp (-P.principalValue * (s + t).val) =
      Real.exp (-P.principalValue * s.val) * Real.exp (-P.principalValue * t.val) := by
    calc
      _ = Real.exp (-P.principalValue * (s.val + t.val)) :=
        congrArg (fun r : ℝ => Real.exp (-P.principalValue * r)) (NNReal.coe_add s t)
      _ = Real.exp (-P.principalValue * s.val + -P.principalValue * t.val) :=
        congrArg Real.exp (mul_add _ _ _)
      _ = _ := Real.exp_add _ _
  rw [map_sub, map_smul, hQ, hphi, reflectedRobinSurvivalOne_eigenbasis_inner, hcoef]
  simp only [smul_eq_mul, reflectedRobinSurvivalFirstCoefficient]
  ring

theorem reflectedRobinAtomicMeanSurvival_ground_remainder_shifted (P : RobinProblem n)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (x : ℝ) :
    |reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) (s + t) -
      Real.exp (-P.principalValue * (s + t).val) *
        reflectedRobinSurvivalFirstCoefficient P (reflectedFold P.length x)| ≤
      reflectedKilledPointConstant P.toSpectralProblem s hs x *
        (Real.exp (-(P.intervalPointProblem.spectralEnumeration 1).1⁻¹ * t.val) *
          ‖reflectedRobinSurvivalGroundRemainder P‖) := by
  rw [← reflectedRobinKilledPointEvaluation_ground_remainder P s hs t x, ← Real.norm_eq_abs]
  exact (reflectedRobinKilledPointEvaluation_bound P s hs x _).trans
    (mul_le_mul_of_nonneg_left (reflectedRobinKilledInterval_survival_ground_remainder_le P t)
      (reflectedKilledPointConstant_nonneg P.toSpectralProblem s hs x))

end TimeTraps.Probability
