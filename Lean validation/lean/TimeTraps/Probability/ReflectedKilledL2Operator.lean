module

public import TimeTraps.Probability.ReflectedKilledL2Contraction
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

theorem reflectedKilledExpectation_add (P : SpectralProblem n) (T : ℝ≥0)
    (f g : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    reflectedKilledExpectation P T (f + g) x =
      reflectedKilledExpectation P T f x + reflectedKilledExpectation P T g x := by
  have he : reflectedKilledValue P T (f + g) x =
      fun ω => reflectedKilledValue P T f x ω + reflectedKilledValue P T g x ω := by
    funext ω
    simp only [reflectedKilledValue, reflectedAtomicWeightedValue, reflectedFellerExtension,
      ContinuousMap.comp_apply, ContinuousMap.add_apply]
    exact mul_add _ _ _
  unfold reflectedKilledExpectation
  rw [he]
  exact integral_add ((reflectedKilledValue_memLp P T f x).integrable (by norm_num))
    ((reflectedKilledValue_memLp P T g x).integrable (by norm_num))

theorem reflectedKilledExpectation_smul (P : SpectralProblem n) (T : ℝ≥0)
    (c : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) (x : ℝ) :
    reflectedKilledExpectation P T (c • f) x = c * reflectedKilledExpectation P T f x := by
  have he : reflectedKilledValue P T (c • f) x = fun ω => c * reflectedKilledValue P T f x ω := by
    funext ω
    simp only [reflectedKilledValue, reflectedAtomicWeightedValue, reflectedFellerExtension,
      ContinuousMap.comp_apply, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  unfold reflectedKilledExpectation
  rw [he, integral_const_mul]

def reflectedKilledContinuousL2 (P : SpectralProblem n) (T : ℝ≥0) :
    C(Icc (0 : ℝ) P.length, ℝ) →ₗ[ℝ] ReflectedUniformL2 P.length P.length_pos where
  toFun f := (reflectedKilledExpectation_memLp P T f).toLp (reflectedKilledExpectation P T f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(reflectedKilledExpectation_memLp P T (f + g)).coeFn_toLp,
      (reflectedKilledExpectation_memLp P T f).coeFn_toLp,
      (reflectedKilledExpectation_memLp P T g).coeFn_toLp,
      Lp.coeFn_add ((reflectedKilledExpectation_memLp P T f).toLp _)
        ((reflectedKilledExpectation_memLp P T g).toLp _)] with x hsum hf hg ha
    rw [hsum, ha]
    dsimp only [Pi.add_apply]
    rw [hf, hg]
    exact reflectedKilledExpectation_add P T f g x
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(reflectedKilledExpectation_memLp P T (c • f)).coeFn_toLp,
      (reflectedKilledExpectation_memLp P T f).coeFn_toLp,
      Lp.coeFn_smul c ((reflectedKilledExpectation_memLp P T f).toLp _)] with x hsum hf hs
    change ((reflectedKilledExpectation_memLp P T (c • f)).toLp _) x =
      (c • ((reflectedKilledExpectation_memLp P T f).toLp _)) x
    rw [hsum, hs]
    dsimp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    exact reflectedKilledExpectation_smul P T c f x

theorem reflectedKilledContinuousL2_coe (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    (reflectedKilledContinuousL2 P T f : ℝ → ℝ) =ᵐ[reflectedUniformLaw P.length P.length_pos]
      reflectedKilledExpectation P T f :=
  (reflectedKilledExpectation_memLp P T f).coeFn_toLp

theorem reflectedKilledContinuousL2_norm (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    ‖reflectedKilledContinuousL2 P T f‖ ≤ ‖reflectedFellerToL2 P.length P.length_pos f‖ := by
  have hi : ‖reflectedFellerToL2 P.length P.length_pos f‖ ^ 2 =
      ∫ x, (reflectedFellerExtension P.length P.length_pos f x) ^ 2
        ∂reflectedUniformLaw P.length P.length_pos := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [reflectedFellerToL2_coe P.length P.length_pos f] with x hx
    simp only [hx, Real.inner_apply, pow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(reflectedKilledExpectation_memLp P T f).toLp (reflectedKilledExpectation P T f)‖ ^ 2 ≤ _
  rw [memLp_norm_toLp_sq, hi]
  exact reflectedKilledExpectation_uniform_sq P T f

def reflectedKilledL2Operator (P : SpectralProblem n) (T : ℝ≥0) :
    ReflectedUniformL2 P.length P.length_pos →L[ℝ] ReflectedUniformL2 P.length P.length_pos :=
  (reflectedKilledContinuousL2 P T).extendOfNorm (reflectedFellerToL2 P.length P.length_pos).toLinearMap

theorem reflectedKilledL2Operator_continuous_input (P : SpectralProblem n) (T : ℝ≥0)
    (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    reflectedKilledL2Operator P T (reflectedFellerToL2 P.length P.length_pos f) =
      reflectedKilledContinuousL2 P T f := by
  apply LinearMap.extendOfNorm_eq (reflectedFellerToL2_denseRange P.length P.length_pos)
  refine ⟨1, fun g => ?_⟩
  change ‖reflectedKilledContinuousL2 P T g‖ ≤ 1 * ‖reflectedFellerToL2 P.length P.length_pos g‖
  rw [one_mul]
  exact reflectedKilledContinuousL2_norm P T g

theorem reflectedKilledL2Operator_norm_le_one (P : SpectralProblem n) (T : ℝ≥0) :
    ‖reflectedKilledL2Operator P T‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (reflectedFellerToL2_denseRange P.length P.length_pos) zero_le_one
  intro f
  change ‖reflectedKilledContinuousL2 P T f‖ ≤ 1 * ‖reflectedFellerToL2 P.length P.length_pos f‖
  rw [one_mul]
  exact reflectedKilledContinuousL2_norm P T f

theorem reflectedKilledL2Operator_contraction (P : SpectralProblem n) (T : ℝ≥0)
    (f : ReflectedUniformL2 P.length P.length_pos) : ‖reflectedKilledL2Operator P T f‖ ≤ ‖f‖ :=
  ((reflectedKilledL2Operator P T).le_opNorm f).trans
    ((mul_le_mul_of_nonneg_right (reflectedKilledL2Operator_norm_le_one P T) (norm_nonneg f)).trans_eq (one_mul _))

end TimeTraps.Probability

end
