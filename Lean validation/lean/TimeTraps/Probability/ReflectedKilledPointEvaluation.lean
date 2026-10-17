module

public import TimeTraps.Probability.ReflectedKilledPointEvaluationBound

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

def reflectedKilledPointLinear (P : SpectralProblem n) (T : ℝ≥0) (x : ℝ) :
    C(Icc (0 : ℝ) P.length, ℝ) →ₗ[ℝ] ℝ where
  toFun f := reflectedKilledExpectation P T f x
  map_add' f g := reflectedKilledExpectation_add P T f g x
  map_smul' c f := reflectedKilledExpectation_smul P T c f x

theorem reflectedKilledPoint_input_dense (P : SpectralProblem n) :
    DenseRange (fun f : C(Icc (0 : ℝ) P.length, ℝ) =>
      reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) :=
  (reflectedUniformL2Equiv P.length P.length_pos).surjective.denseRange.comp
    (reflectedFellerToL2_denseRange P.length P.length_pos)
    (reflectedUniformL2Equiv P.length P.length_pos).continuous

def reflectedKilledPointEvaluation (P : SpectralProblem n) (T : ℝ≥0) (_hT : 0 < T) (x : ℝ) :
    IntervalSobolevL2 0 P.length →L[ℝ] ℝ :=
  (reflectedKilledPointLinear P T x).extendOfNorm
    ((reflectedUniformL2Equiv P.length P.length_pos).toContinuousLinearMap.comp
      (reflectedFellerToL2 P.length P.length_pos)).toLinearMap

theorem reflectedKilledPointEvaluation_continuous_input (P : SpectralProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    reflectedKilledPointEvaluation P T hT x
      (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) =
        reflectedKilledExpectation P T f x := by
  apply LinearMap.extendOfNorm_eq (reflectedKilledPoint_input_dense P)
  refine ⟨reflectedKilledPointConstant P T hT x, fun g => ?_⟩
  change ‖reflectedKilledExpectation P T g x‖ ≤ reflectedKilledPointConstant P T hT x *
    ‖reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos g)‖
  exact reflectedKilledPoint_continuous_bound P T hT x g

theorem reflectedKilledPointEvaluation_norm (P : SpectralProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    ‖reflectedKilledPointEvaluation P T hT x‖ ≤ reflectedKilledPointConstant P T hT x := by
  apply LinearMap.opNorm_extendOfNorm_le (reflectedKilledPoint_input_dense P)
    (reflectedKilledPointConstant_nonneg P T hT x)
  intro f
  change ‖reflectedKilledExpectation P T f x‖ ≤ reflectedKilledPointConstant P T hT x *
    ‖reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)‖
  exact reflectedKilledPoint_continuous_bound P T hT x f

theorem reflectedKilledPointEvaluation_bound (P : SpectralProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (f : IntervalSobolevL2 0 P.length) :
    ‖reflectedKilledPointEvaluation P T hT x f‖ ≤ reflectedKilledPointConstant P T hT x * ‖f‖ :=
  ((reflectedKilledPointEvaluation P T hT x).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (reflectedKilledPointEvaluation_norm P T hT x) (norm_nonneg f))

theorem reflectedKilledPointEvaluation_unique (P : SpectralProblem n)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (A : IntervalSobolevL2 0 P.length →L[ℝ] ℝ)
    (hA : ∀ f : C(Icc (0 : ℝ) P.length, ℝ),
      A (reflectedUniformL2Equiv P.length P.length_pos (reflectedFellerToL2 P.length P.length_pos f)) =
        reflectedKilledExpectation P T f x) : A = reflectedKilledPointEvaluation P T hT x := by
  apply DFunLike.ext'
  apply Continuous.ext_on (reflectedKilledPoint_input_dense P) A.continuous
    (reflectedKilledPointEvaluation P T hT x).continuous
  rintro _ ⟨f, rfl⟩
  rw [hA f, reflectedKilledPointEvaluation_continuous_input]

end TimeTraps.Probability

end
