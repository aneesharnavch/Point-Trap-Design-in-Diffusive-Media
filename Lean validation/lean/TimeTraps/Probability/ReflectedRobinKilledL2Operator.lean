module

public import TimeTraps.Probability.ReflectedRobinKilledL2Contraction
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

/-! The literal killed expectation on continuous tests extends uniquely
by its proved L² bound to the actual spatial L² space. This construction
uses density of continuous functions, not a spectral definition or a
stochastic semigroup assumption. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

theorem reflectedRobinKilledExpectation_add (P : RobinProblem n) (T : ℝ≥0)
    (f g : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    reflectedRobinKilledExpectation P T (f + g) x =
      reflectedRobinKilledExpectation P T f x + reflectedRobinKilledExpectation P T g x := by
  have he : reflectedRobinKilledValue P T (f + g) x =
      fun ω => reflectedRobinKilledValue P T f x ω + reflectedRobinKilledValue P T g x ω := by
    funext ω
    simp only [reflectedRobinKilledValue, reflectedAtomicWeightedValue, reflectedFellerExtension,
      ContinuousMap.comp_apply, ContinuousMap.add_apply]
    exact mul_add _ _ _
  unfold reflectedRobinKilledExpectation
  rw [he]
  exact integral_add ((reflectedRobinKilledValue_memLp P T f x).integrable (by norm_num))
    ((reflectedRobinKilledValue_memLp P T g x).integrable (by norm_num))

theorem reflectedRobinKilledExpectation_smul (P : RobinProblem n) (T : ℝ≥0)
    (c : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    reflectedRobinKilledExpectation P T (c • f) x = c * reflectedRobinKilledExpectation P T f x := by
  have he : reflectedRobinKilledValue P T (c • f) x = fun ω => c * reflectedRobinKilledValue P T f x ω := by
    funext ω
    simp only [reflectedRobinKilledValue, reflectedAtomicWeightedValue, reflectedFellerExtension,
      ContinuousMap.comp_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  unfold reflectedRobinKilledExpectation
  rw [he, integral_const_mul]

def reflectedRobinKilledContinuousL2 (P : RobinProblem n) (T : ℝ≥0) :
    C(Icc (0 : ℝ) P.length, ℝ) →ₗ[ℝ] ReflectedUniformL2 P.length P.length_pos where
  toFun f := (reflectedRobinKilledExpectation_memLp P T f).toLp (reflectedRobinKilledExpectation P T f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(reflectedRobinKilledExpectation_memLp P T (f + g)).coeFn_toLp,
      (reflectedRobinKilledExpectation_memLp P T f).coeFn_toLp,
      (reflectedRobinKilledExpectation_memLp P T g).coeFn_toLp,
      Lp.coeFn_add ((reflectedRobinKilledExpectation_memLp P T f).toLp _)
        ((reflectedRobinKilledExpectation_memLp P T g).toLp _)] with x hsum hf hg ha
    rw [hsum, ha]
    dsimp only [Pi.add_apply]
    rw [hf, hg]
    exact reflectedRobinKilledExpectation_add P T f g x
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(reflectedRobinKilledExpectation_memLp P T (c • f)).coeFn_toLp,
      (reflectedRobinKilledExpectation_memLp P T f).coeFn_toLp,
      Lp.coeFn_smul c ((reflectedRobinKilledExpectation_memLp P T f).toLp _)] with x hsum hf hs
    change ((reflectedRobinKilledExpectation_memLp P T (c • f)).toLp _) x =
      (c • ((reflectedRobinKilledExpectation_memLp P T f).toLp _)) x
    rw [hsum, hs]
    dsimp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    exact reflectedRobinKilledExpectation_smul P T c f x

theorem reflectedRobinKilledContinuousL2_coe (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    (reflectedRobinKilledContinuousL2 P T f : ℝ → ℝ) =ᵐ[reflectedUniformLaw P.length P.length_pos]
      reflectedRobinKilledExpectation P T f :=
  (reflectedRobinKilledExpectation_memLp P T f).coeFn_toLp

theorem reflectedRobinKilledContinuousL2_norm (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    ‖reflectedRobinKilledContinuousL2 P T f‖ ≤ ‖reflectedFellerToL2 P.length P.length_pos f‖ := by
  have hi : ‖reflectedFellerToL2 P.length P.length_pos f‖ ^ 2 =
      ∫ x, (reflectedFellerExtension P.length P.length_pos f x) ^ 2
        ∂reflectedUniformLaw P.length P.length_pos := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [reflectedFellerToL2_coe P.length P.length_pos f] with x hx
    simp only [hx, Real.inner_apply, pow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(reflectedRobinKilledExpectation_memLp P T f).toLp (reflectedRobinKilledExpectation P T f)‖ ^ 2 ≤ _
  rw [memLp_norm_toLp_sq, hi]
  exact reflectedRobinKilledExpectation_uniform_sq P T f

def reflectedRobinKilledL2Operator (P : RobinProblem n) (T : ℝ≥0) :
    ReflectedUniformL2 P.length P.length_pos →L[ℝ] ReflectedUniformL2 P.length P.length_pos :=
  (reflectedRobinKilledContinuousL2 P T).extendOfNorm (reflectedFellerToL2 P.length P.length_pos).toLinearMap

theorem reflectedRobinKilledL2Operator_continuous_input (P : RobinProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    reflectedRobinKilledL2Operator P T (reflectedFellerToL2 P.length P.length_pos f) =
      reflectedRobinKilledContinuousL2 P T f := by
  apply LinearMap.extendOfNorm_eq (reflectedFellerToL2_denseRange P.length P.length_pos)
  refine ⟨1, fun g => ?_⟩
  change ‖reflectedRobinKilledContinuousL2 P T g‖ ≤ 1 * ‖reflectedFellerToL2 P.length P.length_pos g‖
  rw [one_mul]
  exact reflectedRobinKilledContinuousL2_norm P T g

theorem reflectedRobinKilledL2Operator_norm_le_one (P : RobinProblem n) (T : ℝ≥0) :
    ‖reflectedRobinKilledL2Operator P T‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (reflectedFellerToL2_denseRange P.length P.length_pos) zero_le_one
  intro f
  change ‖reflectedRobinKilledContinuousL2 P T f‖ ≤ 1 * ‖reflectedFellerToL2 P.length P.length_pos f‖
  rw [one_mul]
  exact reflectedRobinKilledContinuousL2_norm P T f

theorem reflectedRobinKilledL2Operator_contraction (P : RobinProblem n) (T : ℝ≥0)
    (f : ReflectedUniformL2 P.length P.length_pos) : ‖reflectedRobinKilledL2Operator P T f‖ ≤ ‖f‖ :=
  ((reflectedRobinKilledL2Operator P T).le_opNorm f).trans
    ((mul_le_mul_of_nonneg_right (reflectedRobinKilledL2Operator_norm_le_one P T) (norm_nonneg f)).trans_eq (one_mul _))

end TimeTraps.Probability

end
