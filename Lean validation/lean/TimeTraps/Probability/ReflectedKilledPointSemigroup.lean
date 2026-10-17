module

public import TimeTraps.Probability.ReflectedKilledPointEvaluationEigenstate
public import TimeTraps.Probability.ReflectedKilledSpectralSemigroup

@[expose] public section

/-! Positive-time actual point evaluation composes with the killed
L² semigroup. The identity is proved on the complete actual eigenbasis
and extended by continuity, giving every-start continuous-test formulas
without assuming a pathwise additive-functional cocycle. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ}

theorem reflectedKilledPointEvaluation_add (P : SpectralProblem n)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (x : ℝ) :
    reflectedKilledPointEvaluation P (s + t) (add_pos_of_pos_of_nonneg hs (show 0 ≤ t from zero_le)) x =
      (reflectedKilledPointEvaluation P s hs x).comp (reflectedKilledIntervalL2Operator P t) := by
  have hcoef (ev : ℝ) : Real.exp (-ev * (s + t).val) =
      Real.exp (-ev * t.val) * Real.exp (-ev * s.val) := by
    calc
      _ = Real.exp (-ev * (s.val + t.val)) := congrArg (fun r : ℝ => Real.exp (-ev * r)) (NNReal.coe_add s t)
      _ = Real.exp (-ev * s.val + -ev * t.val) := congrArg Real.exp (mul_add _ _ _)
      _ = Real.exp (-ev * s.val) * Real.exp (-ev * t.val) := Real.exp_add _ _
      _ = _ := mul_comm _ _
  apply ContinuousLinearMap.ext_on (s := Set.range P.intervalPointProblem.eigenbasis)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr P.intervalPointProblem.eigenbasis.dense_span)
  rintro _ ⟨i, rfl⟩
  change reflectedKilledPointEvaluation P (s + t) _ x (P.intervalPointProblem.eigenbasis i) =
    reflectedKilledPointEvaluation P s hs x
      (reflectedKilledIntervalL2Operator P t (P.intervalPointProblem.eigenbasis i))
  rw [reflectedKilledPointEvaluation_eigenbasis, reflectedKilledIntervalL2Operator_eigenbasis,
    map_smul, reflectedKilledPointEvaluation_eigenbasis]
  change Real.exp (-i.1⁻¹ * (s + t).val) *
      (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x) =
    Real.exp (-i.1⁻¹ * t.val) * (Real.exp (-i.1⁻¹ * s.val) *
      (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x))
  exact (congrArg (fun r : ℝ => r *
    (P.intervalPointProblem.eigenstate i).representative P.length_pos (reflectedFold P.length x))
      (hcoef i.1⁻¹)).trans (mul_assoc _ _ _)

theorem reflectedKilledPointEvaluation_add_apply (P : SpectralProblem n)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (x : ℝ) (f : IntervalSobolevL2 0 P.length) :
    reflectedKilledPointEvaluation P (s + t) (add_pos_of_pos_of_nonneg hs (show 0 ≤ t from zero_le)) x f =
      reflectedKilledPointEvaluation P s hs x (reflectedKilledIntervalL2Operator P t f) :=
  congrArg (fun A : IntervalSobolevL2 0 P.length →L[ℝ] ℝ => A f)
    (reflectedKilledPointEvaluation_add P s hs t x)

theorem reflectedKilledExpectation_time_split (P : SpectralProblem n)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (x : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    reflectedKilledExpectation P (s + t) f x =
      reflectedKilledPointEvaluation P s hs x
        (reflectedKilledIntervalL2Operator P t
          (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f))) := by
  rw [← reflectedKilledPointEvaluation_continuous_input P (s + t)
    (add_pos_of_pos_of_nonneg hs (show 0 ≤ t from zero_le)) x f]
  exact reflectedKilledPointEvaluation_add_apply P s hs t x _

end TimeTraps.Probability
