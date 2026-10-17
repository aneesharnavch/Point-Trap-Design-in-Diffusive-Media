module

public import TimeTraps.Probability.ReflectedRobinKilledPointEvaluationBound

@[expose] public section

/-! Positive-time evaluation of the actual killed expectation extends
to a bounded linear functional on Lebesgue L². The extension agrees with
every continuous test at the fixed start, not merely almost every start.
No choice of a pointwise representative for arbitrary L² input is made. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

def reflectedRobinKilledPointLinear (P : RobinProblem n) (T : ℝ≥0) (x : ℝ) :
    C(Icc (0 : ℝ) P.length, ℝ) →ₗ[ℝ] ℝ where
  toFun f := reflectedRobinKilledExpectation P T f x
  map_add' f g := reflectedRobinKilledExpectation_add P T f g x
  map_smul' c f := reflectedRobinKilledExpectation_smul P T c f x

theorem reflectedRobinKilledPoint_input_dense (P : RobinProblem n) :
    DenseRange (fun f : C(Icc (0 : ℝ) P.length, ℝ) =>
      reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) :=
  (reflectedUniformL2Equiv P.length P.length_pos).surjective.denseRange.comp
    (reflectedFellerToL2_denseRange P.length P.length_pos)
    (reflectedUniformL2Equiv P.length P.length_pos).continuous

def reflectedRobinKilledPointEvaluation (P : RobinProblem n) (T : ℝ≥0) (_hT : 0 < T) (x : ℝ) :
    IntervalSobolevL2 0 P.length →L[ℝ] ℝ :=
  (reflectedRobinKilledPointLinear P T x).extendOfNorm
    ((reflectedUniformL2Equiv P.length P.length_pos).toContinuousLinearMap.comp
      (reflectedFellerToL2 P.length P.length_pos)).toLinearMap

theorem reflectedRobinKilledPointEvaluation_continuous_input (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    reflectedRobinKilledPointEvaluation P T hT x
      (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) =
        reflectedRobinKilledExpectation P T f x := by
  apply LinearMap.extendOfNorm_eq (reflectedRobinKilledPoint_input_dense P)
  refine ⟨reflectedKilledPointConstant P.toSpectralProblem T hT x, fun g => ?_⟩
  change ‖reflectedRobinKilledExpectation P T g x‖ ≤ reflectedKilledPointConstant P.toSpectralProblem T hT x *
    ‖reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos g)‖
  exact reflectedRobinKilledPoint_continuous_bound P T hT x g

theorem reflectedRobinKilledPointEvaluation_norm (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    ‖reflectedRobinKilledPointEvaluation P T hT x‖ ≤ reflectedKilledPointConstant P.toSpectralProblem T hT x := by
  apply LinearMap.opNorm_extendOfNorm_le (reflectedRobinKilledPoint_input_dense P)
    (reflectedKilledPointConstant_nonneg P.toSpectralProblem T hT x)
  intro f
  change ‖reflectedRobinKilledExpectation P T f x‖ ≤ reflectedKilledPointConstant P.toSpectralProblem T hT x *
    ‖reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)‖
  exact reflectedRobinKilledPoint_continuous_bound P T hT x f

theorem reflectedRobinKilledPointEvaluation_bound (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (f : IntervalSobolevL2 0 P.length) :
    ‖reflectedRobinKilledPointEvaluation P T hT x f‖ ≤ reflectedKilledPointConstant P.toSpectralProblem T hT x * ‖f‖ :=
  ((reflectedRobinKilledPointEvaluation P T hT x).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (reflectedRobinKilledPointEvaluation_norm P T hT x) (norm_nonneg f))

theorem reflectedRobinKilledPointEvaluation_unique (P : RobinProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (A : IntervalSobolevL2 0 P.length →L[ℝ] ℝ)
    (hA : ∀ f : C(Icc (0 : ℝ) P.length, ℝ),
      A (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) =
        reflectedRobinKilledExpectation P T f x) : A = reflectedRobinKilledPointEvaluation P T hT x := by
  apply DFunLike.ext'
  apply Continuous.ext_on (reflectedRobinKilledPoint_input_dense P) A.continuous
    (reflectedRobinKilledPointEvaluation P T hT x).continuous
  rintro _ ⟨f, rfl⟩
  rw [hA f, reflectedRobinKilledPointEvaluation_continuous_input]

end TimeTraps.Probability

end
