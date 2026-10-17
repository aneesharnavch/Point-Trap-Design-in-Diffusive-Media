module

public import TimeTraps.Probability.ReflectedRobinKilledPointEvaluation
public import TimeTraps.Probability.ReflectedRobinKilledEigenbasis

@[expose] public section

/-! The actual positive-time evaluation functional acts on every physical
weak eigenstate by its proved exponential factor at the fixed start.
The complete operator eigenbasis is a specialization; no positivity of
the eigenfunction or pointwise L² representative is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace
open scoped NNReal

variable {n : ℕ} {P : RobinProblem n} {ev : ℝ} {u : ℝ → ℝ}

theorem reflectedRobinKilledPointEvaluation_weak_eigenstate (hu : RobinWeakEigenEquation P ev u)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    reflectedRobinKilledPointEvaluation P T hT x (ofEnergy hu.energy P.length_pos).state =
      Real.exp (-ev * T.val) * u (reflectedFold P.length x) := by
  rw [← reflectedRobinWeakEigenstate_profile_intervalL2 hu,
    reflectedRobinKilledPointEvaluation_continuous_input, reflectedRobinKilledExpectation_weak_profile hu T x]
  exact reflectedRobinWeakEigenstate_expectation hu x T

theorem reflectedRobinKilledPointEvaluation_eigenbasis (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    reflectedRobinKilledPointEvaluation P T hT x (P.intervalPointProblem.eigenbasis i) =
      Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x) := by
  have he := reflectedRobinKilledPointEvaluation_weak_eigenstate (P.interval_eigenbasis_weak i) T hT x
  have hu : ofEnergy (P.interval_eigenbasis_weak i).energy P.length_pos =
      P.intervalPointProblem.eigenstate i :=
    ofEnergy_representative (P.intervalPointProblem.eigenstate i) P.length_pos
  rw [hu, P.intervalPointProblem.eigenstate_state] at he
  exact he

end TimeTraps.Probability
