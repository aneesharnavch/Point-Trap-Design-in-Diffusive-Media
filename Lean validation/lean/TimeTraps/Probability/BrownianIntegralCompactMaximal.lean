module

public import TimeTraps.Probability.BrownianIntegralCompactMaximalApproximation
public import TimeTraps.Probability.BrownianIntegralCompactMaximalFatou

@[expose] public section

/-! The actual compact supremum of a finite elementary-sum integral is
square-integrable and obeys the constant-four maximal bound. Its regular
representative is an actual L² random variable with values in C([0,T],ℝ).
The original explicit path has the same compact supremum almost surely.
The finite index type may be empty and the horizon may be zero. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {I : Type*} [Fintype I]

theorem brownianElementaryCompactMax_L2 (a : I → BrownianDyadicElementary) (T : ℝ≥0) :
    MemLp (brownianElementaryCompactMax a T) 2 brownianDyadicMeasure ∧
      (∫ ω, brownianElementaryCompactMax a T ω ^ 2 ∂brownianDyadicMeasure) ≤
        4 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
          brownianDyadicMeasure T (brownianElementarySumIntegrand a)‖ ^ 2 := by
  have hb : ∀ n, (∫ ω, brownianElementaryCompactMaxApprox a T n ω ^ 2 ∂brownianDyadicMeasure) ≤
      (2 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T (brownianElementarySumIntegrand a)‖) ^ 2 := by
    intro n
    convert brownianElementaryCompactMaxApprox_secondMoment_le a T n using 1
    ring
  have h := compactMaximal_memLp_of_tendsto (by positivity)
    (brownianElementaryCompactMaxApprox_memLp a T)
    (brownianElementaryCompactMax_measurable a T).aestronglyMeasurable
    (Eventually.of_forall (brownianElementaryCompactMaxApprox_tendsto a T)) hb
  simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem brownianElementaryCompactPath_memLp (a : I → BrownianDyadicElementary) (T : ℝ≥0) :
    MemLp (brownianElementaryCompactPath a T) 2 brownianDyadicMeasure :=
  (memLp_norm_iff (brownianElementaryCompactPath_stronglyMeasurable a T).aestronglyMeasurable).mp
    (brownianElementaryCompactMax_L2 a T).1

def brownianElementaryCompactPathL2 (a : I → BrownianDyadicElementary) (T : ℝ≥0) :
    Lp C(BrownianCompactTime T, ℝ) 2 brownianDyadicMeasure :=
  (brownianElementaryCompactPath_memLp a T).toLp (brownianElementaryCompactPath a T)

theorem brownianElementaryCompactPathL2_coe (a : I → BrownianDyadicElementary) (T : ℝ≥0) :
    brownianElementaryCompactPathL2 a T =ᵐ[brownianDyadicMeasure]
      brownianElementaryCompactPath a T :=
  (brownianElementaryCompactPath_memLp a T).coeFn_toLp

theorem brownianElementaryCompactPathL2_norm_le (a : I → BrownianDyadicElementary) (T : ℝ≥0) :
    ‖brownianElementaryCompactPathL2 a T‖ ≤
      2 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T (brownianElementarySumIntegrand a)‖ := by
  have he : eLpNorm (brownianElementaryCompactPath a T) 2 brownianDyadicMeasure =
      eLpNorm (brownianElementaryCompactMax a T) 2 brownianDyadicMeasure :=
    (eLpNorm_norm (brownianElementaryCompactPath a T)).symm
  have hn : ‖brownianElementaryCompactPathL2 a T‖ =
      ‖(brownianElementaryCompactMax_L2 a T).1.toLp (brownianElementaryCompactMax a T)‖ := by
    rw [brownianElementaryCompactPathL2, Lp.norm_toLp, Lp.norm_toLp, he]
  rw [hn]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [TimeTraps.Analysis.memLp_norm_toLp_sq]
  nlinarith [(brownianElementaryCompactMax_L2 a T).2]

theorem brownianElementaryCompactPathL2_martingale_ae (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) (t : BrownianCompactTime T) :
    (fun ω => brownianElementaryCompactPathL2 a T ω t) =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralProcess (brownianElementarySumIntegrand a) t.val := by
  have he : (fun ω => brownianElementaryCompactPathL2 a T ω t) =ᵐ[brownianDyadicMeasure]
      brownianElementaryRegularPath a t.val :=
    (brownianElementaryCompactPathL2_coe a T).mono (fun _ hω => congrArg (fun f => f t) hω)
  exact he.trans (brownianElementaryRegularPath_martingale_ae a t.val)

theorem brownianElementarySumPath_sup_memLp (a : I → BrownianDyadicElementary) (T : ℝ≥0) :
    MemLp (fun ω => ⨆ t : BrownianCompactTime T, |brownianElementarySumPath a t.val ω|)
      2 brownianDyadicMeasure :=
  (brownianElementaryCompactMax_L2 a T).1.ae_eq
    (brownianElementaryCompactMax_eq_original_sup_ae a T)

theorem brownianElementarySumPath_sup_secondMoment_le (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) :
    (∫ ω, (⨆ t : BrownianCompactTime T, |brownianElementarySumPath a t.val ω|) ^ 2
      ∂brownianDyadicMeasure) ≤
      4 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T (brownianElementarySumIntegrand a)‖ ^ 2 := by
  have he : (∫ ω, (⨆ t : BrownianCompactTime T, |brownianElementarySumPath a t.val ω|) ^ 2
      ∂brownianDyadicMeasure) =
      ∫ ω, brownianElementaryCompactMax a T ω ^ 2 ∂brownianDyadicMeasure := by
    apply integral_congr_ae
    exact (brownianElementaryCompactMax_eq_original_sup_ae a T).mono
      (fun _ hω => congrArg (fun x : ℝ => x ^ 2) hω.symm)
  rw [he]
  exact (brownianElementaryCompactMax_L2 a T).2

end TimeTraps.Probability

end
