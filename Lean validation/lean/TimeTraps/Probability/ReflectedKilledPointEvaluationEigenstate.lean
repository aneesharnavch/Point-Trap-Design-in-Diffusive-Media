module

public import TimeTraps.Probability.ReflectedKilledPointEvaluation
public import TimeTraps.Probability.ReflectedKilledEigenbasis

@[expose] public section

/-! The actual positive-time evaluation functional acts on every physical
weak eigenstate by its proved exponential factor at the fixed start.
The complete operator eigenbasis is a specialization; no positivity of
the eigenfunction or pointwise L² representative is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis TimeTraps.Spectral IntervalSobolevSpace
open scoped NNReal

variable {n : ℕ} {P : SpectralProblem n} {ev : ℝ} {u : ℝ → ℝ}

theorem reflectedKilledPointEvaluation_weak_eigenstate (hu : WeakEigenEquation P ev u)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    reflectedKilledPointEvaluation P T hT x (ofEnergy hu.energy P.length_pos).state =
      Real.exp (-ev * T.val) * u (reflectedFold P.length x) := by
  rw [← reflectedWeakEigenstate_profile_intervalL2 hu,
    reflectedKilledPointEvaluation_continuous_input, reflectedKilledExpectation_weak_profile hu T x]
  exact reflectedWeakEigenstate_expectation hu x T

theorem reflectedKilledPointEvaluation_eigenbasis (P : SpectralProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (i : CompactSpectralIndex P.intervalPointProblem.inverse) :
    reflectedKilledPointEvaluation P T hT x (P.intervalPointProblem.eigenbasis i) =
      Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x) := by
  have he := reflectedKilledPointEvaluation_weak_eigenstate (P.interval_eigenbasis_weak i) T hT x
  have hu : ofEnergy (P.interval_eigenbasis_weak i).energy P.length_pos =
      P.intervalPointProblem.eigenstate i :=
    ofEnergy_representative (P.intervalPointProblem.eigenstate i) P.length_pos
  rw [hu, P.intervalPointProblem.eigenstate_state] at he
  exact he

end TimeTraps.Probability
