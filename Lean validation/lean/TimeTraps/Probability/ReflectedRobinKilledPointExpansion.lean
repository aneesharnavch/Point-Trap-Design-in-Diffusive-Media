module

public import TimeTraps.Probability.ReflectedRobinKilledPointSemigroup

@[expose] public section

/-! At every start and every positive time, the actual Robin killed
expectation has the complete original operator eigenfunction expansion.
The point functional is constructed from the actual stochastic expectation
and its Gaussian bound before using the spectral basis. -/

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal

variable {n : ℕ}

theorem reflectedRobinKilledPointEvaluation_hasSum (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (f : IntervalSobolevL2 0 P.length) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      inner ℝ (P.intervalPointProblem.eigenbasis i) f * Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x))
      (reflectedRobinKilledPointEvaluation P T hT x f) := by
  have h := (P.intervalPointProblem.eigenbasis_expansion f).mapL
    (reflectedRobinKilledPointEvaluation P T hT x)
  apply h.congr
  intro s
  apply Finset.sum_congr rfl
  intro i _
  change reflectedRobinKilledPointEvaluation P T hT x
    (inner ℝ (P.intervalPointProblem.eigenbasis i) f • P.intervalPointProblem.eigenbasis i) = _
  rw [map_smul, reflectedRobinKilledPointEvaluation_eigenbasis]
  exact (mul_assoc _ _ _).symm

theorem reflectedRobinKilledExpectation_hasSum (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    HasSum (fun i : CompactSpectralIndex P.intervalPointProblem.inverse =>
      inner ℝ (P.intervalPointProblem.eigenbasis i)
        (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) *
        Real.exp (-i.1⁻¹ * T.val) *
        (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x))
      (reflectedRobinKilledExpectation P T f x) := by
  rw [← reflectedRobinKilledPointEvaluation_continuous_input P T hT x f]
  exact reflectedRobinKilledPointEvaluation_hasSum P T hT x _

theorem reflectedRobinKilledPointEvaluation_heat_split (P : RobinProblem n)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (x : ℝ) (f : IntervalSobolevL2 0 P.length) :
    reflectedRobinKilledPointEvaluation P (s + t) (add_pos_of_pos_of_nonneg hs (show 0 ≤ t from zero_le)) x f =
      reflectedRobinKilledPointEvaluation P s hs x
        (P.intervalPointProblem.compactPositiveInverse.heatSemigroup t f) := by
  rw [← reflectedRobinKilledIntervalL2Operator_eq_heat]
  exact reflectedRobinKilledPointEvaluation_add_apply P s hs t x f

end TimeTraps.Probability
