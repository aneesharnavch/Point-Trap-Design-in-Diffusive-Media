module

public import TimeTraps.Probability.ReflectedRobinSurvivalSeriesData
public import TimeTraps.Probability.ReflectedRobinSurvivalHeatRemainder

@[expose] public section

/-! The constant-one L² input represents literal survival. Its first
spectral coefficient is the integral of the actual H¹ first mode, so
the leading survival coefficient is positive at every physical start,
independently of the arbitrary sign of the chosen Hilbert basis vector. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace
open scoped NNReal ENNReal Topology

variable {n : ℕ}

noncomputable def reflectedRobinSurvivalFirstCoefficient (P : RobinProblem n) (x : ℝ) : ℝ :=
  (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
    P.length_pos x * ∫ y in (0 : ℝ)..P.length,
      (P.intervalPointProblem.eigenstate (P.intervalPointProblem.spectralEnumeration 0)).representative
        P.length_pos y

noncomputable def reflectedRobinSurvivalGroundRemainder (P : RobinProblem n) : IntervalSobolevL2 0 P.length :=
  reflectedRobinSurvivalOne P -
    inner ℝ (P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0))
      (reflectedRobinSurvivalOne P) • P.intervalPointProblem.eigenbasis (P.intervalPointProblem.spectralEnumeration 0)

theorem reflectedRobinSurvivalFirstCoefficient_pos (P : RobinProblem n)
    {x : ℝ} (hx : x ∈ Icc 0 P.length) : 0 < reflectedRobinSurvivalFirstCoefficient P x :=
  P.interval_first_survival_coefficient_pos hx

end TimeTraps.Probability
