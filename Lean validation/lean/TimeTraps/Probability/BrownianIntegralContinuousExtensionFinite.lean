module

public import TimeTraps.Probability.BrownianIntegralContinuousExtensionBound

@[expose] public section

/-! Finite linear combinations of elementary continuous path variables.
Their evaluations are the actual cutoff integral of the corresponding
product-L² integrand, so the compact maximal estimate proves the bound
needed to descend finite presentations and extend to the closed span. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

def brownianContinuousGenerator (T : ℝ≥0) (a : BrownianDyadicElementary) :
    BrownianCompactPathL2 T :=
  brownianElementaryCompactPathL2 (fun _ : Unit => a) T

theorem brownianContinuousGenerator_evaluation (T : ℝ≥0) (t : BrownianCompactTime T)
    (a : BrownianDyadicElementary) :
    brownianCompactEvaluation T t (brownianContinuousGenerator T a) =
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t.val (brownianIntegralGenerator a) := by
  apply Lp.ext
  have hp := brownianElementaryCompactPathL2_martingale_ae (fun _ : Unit => a) T t
  have hs : brownianElementarySumIntegrand (fun _ : Unit => a) = brownianIntegralGenerator a := by
    simp [brownianElementarySumIntegrand]
  rw [hs] at hp
  exact (brownianCompactEvaluation_coe T t (brownianContinuousGenerator T a)).trans
    (hp.trans (brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal _ t.val))

def brownianIntegrandCombination : (BrownianDyadicElementary →₀ ℝ) →ₗ[ℝ] BrownianIntegrand :=
  Finsupp.linearCombination ℝ brownianIntegralGenerator

def brownianContinuousCombination (T : ℝ≥0) :
    (BrownianDyadicElementary →₀ ℝ) →ₗ[ℝ] BrownianCompactPathL2 T :=
  Finsupp.linearCombination ℝ (brownianContinuousGenerator T)

theorem brownianIntegrandCombination_coe (c : BrownianDyadicElementary →₀ ℝ) :
    (brownianIntegrandCombination c : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) =
      Finsupp.linearCombination ℝ (fun a : BrownianDyadicElementary => a.processL2) c := by
  change (brownianIntegralSpace brownianDyadicPath brownianDyadicPath_measurable
    brownianDyadicMeasure).subtype (Finsupp.linearCombination ℝ brownianIntegralGenerator c) = _
  rw [Finsupp.apply_linearCombination]
  rfl

theorem brownianIntegrandCombination_dense : DenseRange brownianIntegrandCombination := by
  have hsub : Set.range (TimeTraps.Analysis.gramClosureInclusion
      (fun a : BrownianDyadicElementary => a.processL2)) ⊆ Set.range brownianIntegrandCombination := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨c, hc⟩ := (show (z : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) ∈
        (Finsupp.linearCombination ℝ (fun a : BrownianDyadicElementary => a.processL2)).range by
      rw [Finsupp.range_linearCombination]
      exact z.property)
    refine ⟨c, Subtype.ext ?_⟩
    rw [brownianIntegrandCombination_coe]
    exact hc
  exact (TimeTraps.Analysis.gramClosureInclusion_dense
    (fun a : BrownianDyadicElementary => a.processL2)).mono hsub

theorem brownianContinuousCombination_evaluation (T : ℝ≥0) (t : BrownianCompactTime T)
    (c : BrownianDyadicElementary →₀ ℝ) :
    brownianCompactEvaluation T t (brownianContinuousCombination T c) =
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t.val (brownianIntegrandCombination c) := by
  change (brownianCompactEvaluation T t).toLinearMap
      (Finsupp.linearCombination ℝ (brownianContinuousGenerator T) c) =
    (brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t.val).toLinearMap
      (Finsupp.linearCombination ℝ brownianIntegralGenerator c)
  rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination]
  have he : (brownianCompactEvaluation T t).toLinearMap ∘ brownianContinuousGenerator T =
      (brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t.val).toLinearMap ∘
        brownianIntegralGenerator :=
    funext (brownianContinuousGenerator_evaluation T t)
  rw [he]

theorem brownianContinuousCombination_norm_le (T : ℝ≥0) (c : BrownianDyadicElementary →₀ ℝ) :
    ‖brownianContinuousCombination T c‖ ≤
      2 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T (brownianIntegrandCombination c)‖ := by
  apply brownianCompactPathL2_norm_le
  intro t
  have he := (brownianCompactEvaluation_coe T t (brownianContinuousCombination T c)).symm
  rw [brownianContinuousCombination_evaluation] at he
  exact he.trans (brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal _ t.val).symm

theorem brownianContinuousCombination_bound (T : ℝ≥0) (c : BrownianDyadicElementary →₀ ℝ) :
    ‖brownianContinuousCombination T c‖ ≤ 2 * ‖brownianIntegrandCombination c‖ :=
  (brownianContinuousCombination_norm_le T c).trans
    (mul_le_mul_of_nonneg_left (brownianTimeCutoff_norm_le T (brownianIntegrandCombination c))
      (by norm_num))

end TimeTraps.Probability

end
