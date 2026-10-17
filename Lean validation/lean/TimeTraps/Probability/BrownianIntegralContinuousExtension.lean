module

public import TimeTraps.Probability.BrownianIntegralContinuousExtensionFinite

@[expose] public section

/-! The finite continuous-path map extends to every element of the
existing completed product-L² integrand space. The target is the Banach
space L²(Ω;C([0,T],ℝ)); no density in a larger predictable space is used. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

def brownianIntegralContinuousL2 (T : ℝ≥0) : BrownianIntegrand →L[ℝ] BrownianCompactPathL2 T :=
  (brownianContinuousCombination T).extendOfNorm brownianIntegrandCombination

theorem brownianIntegralContinuousL2_combination (T : ℝ≥0) (c : BrownianDyadicElementary →₀ ℝ) :
    brownianIntegralContinuousL2 T (brownianIntegrandCombination c) = brownianContinuousCombination T c :=
  LinearMap.extendOfNorm_eq brownianIntegrandCombination_dense
    ⟨2, brownianContinuousCombination_bound T⟩ c

theorem brownianIntegralContinuousL2_generator (T : ℝ≥0) (a : BrownianDyadicElementary) :
    brownianIntegralContinuousL2 T (brownianIntegralGenerator a) = brownianContinuousGenerator T a := by
  simpa only [brownianIntegrandCombination, brownianContinuousCombination,
    Finsupp.linearCombination_single, one_smul] using
    brownianIntegralContinuousL2_combination T (Finsupp.single a 1)

theorem brownianIntegralContinuousL2_evaluation (T : ℝ≥0) (t : BrownianCompactTime T)
    (f : BrownianIntegrand) :
    brownianCompactEvaluation T t (brownianIntegralContinuousL2 T f) =
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t.val f := by
  refine brownianIntegrandCombination_dense.induction_on f
    (isClosed_eq ((brownianCompactEvaluation T t).continuous.comp
      (brownianIntegralContinuousL2 T).continuous)
      (brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t.val).continuous) ?_
  intro c
  rw [brownianIntegralContinuousL2_combination, brownianContinuousCombination_evaluation]

theorem brownianIntegralContinuousL2_evaluation_ae (T : ℝ≥0) (t : BrownianCompactTime T)
    (f : BrownianIntegrand) :
    (fun ω => brownianIntegralContinuousL2 T f ω t) =ᵐ[brownianDyadicMeasure]
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t.val f := by
  have h := (brownianCompactEvaluation_coe T t (brownianIntegralContinuousL2 T f)).symm
  rw [brownianIntegralContinuousL2_evaluation] at h
  exact h

theorem brownianIntegralContinuousL2_norm_le (T : ℝ≥0) (f : BrownianIntegrand) :
    ‖brownianIntegralContinuousL2 T f‖ ≤
      2 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure T f‖ := by
  apply brownianCompactPathL2_norm_le
  intro t
  exact (brownianIntegralContinuousL2_evaluation_ae T t f).trans
    (brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal f t.val).symm

theorem brownianIntegralContinuousL2_bound (T : ℝ≥0) (f : BrownianIntegrand) :
    ‖brownianIntegralContinuousL2 T f‖ ≤ 2 * ‖f‖ :=
  (brownianIntegralContinuousL2_norm_le T f).trans
    (mul_le_mul_of_nonneg_left (brownianTimeCutoff_norm_le T f) (by norm_num))

theorem brownianCompactPathL2_ext {T : ℝ≥0} (F G : BrownianCompactPathL2 T)
    (h : ∀ t : BrownianCompactTime T, brownianCompactEvaluation T t F = brownianCompactEvaluation T t G) :
    F = G := by
  apply Lp.ext
  have ht : ∀ t : BrownianCompactTime T, (fun ω => F ω t) =ᵐ[brownianDyadicMeasure] (fun ω => G ω t) := by
    intro t
    have hF := (brownianCompactEvaluation_coe T t F).symm
    rw [h t] at hF
    exact hF.trans (brownianCompactEvaluation_coe T t G)
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      F ω (denseSeq (BrownianCompactTime T) n) = G ω (denseSeq (BrownianCompactTime T) n) :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime T) n))
  filter_upwards [hall] with ω hω
  apply ContinuousMap.coe_injective
  exact (denseRange_denseSeq (BrownianCompactTime T)).equalizer (F ω).continuous (G ω).continuous
    (funext hω)

theorem brownianIntegralContinuousL2_elementarySum {I : Type*} [Fintype I]
    (T : ℝ≥0) (a : I → BrownianDyadicElementary) :
    brownianIntegralContinuousL2 T (brownianElementarySumIntegrand a) = brownianElementaryCompactPathL2 a T := by
  apply brownianCompactPathL2_ext
  intro t
  rw [brownianIntegralContinuousL2_evaluation]
  apply Lp.ext
  exact ((brownianCompactEvaluation_coe T t (brownianElementaryCompactPathL2 a T)).trans
    ((brownianElementaryCompactPathL2_martingale_ae a T t).trans
      (brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal _ t.val))).symm

end TimeTraps.Probability

end
