module

public import TimeTraps.Probability.ReflectedKilledPointEvaluationBound
public import TimeTraps.Probability.ReflectedRobinKilledL2Interval

@[expose] public section

/-! A fixed positive-time killed expectation is bounded by the actual
Lebesgue L² norm of its continuous input. The constant is the square root
of the finite reference-density bound; it may depend on time and start. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

theorem reflectedRobinKilledPoint_continuous_bound (P : RobinProblem n) (T : ℝ≥0) (hT : 0 < T)
    (x : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    ‖reflectedRobinKilledExpectation P T f x‖ ≤ reflectedKilledPointConstant P.toSpectralProblem T hT x *
      ‖reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)‖ := by
  have he := (reflectedRobinKilledExpectation_sq_le P T f x).trans
    (reflectedKilledPoint_kernel_sq_bound P.toSpectralProblem T hT x f)
  rw [← reflectedKilledPoint_input_norm_sq P.toSpectralProblem f] at he
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (reflectedKilledPointConstant_nonneg P.toSpectralProblem T hT x) (norm_nonneg _))).mp
  rw [mul_pow, reflectedKilledPointConstant, Real.sq_sqrt (norm_nonneg _)]
  simpa only [Real.norm_eq_abs, sq_abs] using he

end TimeTraps.Probability

end
