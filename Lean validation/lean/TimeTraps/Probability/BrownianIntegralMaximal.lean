module

public import TimeTraps.Probability.BrownianIntegralMaximalDiscrete
public import TimeTraps.Probability.BrownianIntegralMaximalGrid

@[expose] public section

/-! Exact finite-grid L² maximal bounds for the actual integral martingale.
A grid is indexed by Fin (N+1), is nondecreasing, and ends no later than T.
It may have one point or repeated times; its first time need not be zero. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem brownianIntegralGridMax_memLp (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) :
    MemLp (brownianIntegralGridMax hB f τ) 2 P := by
  have h2 (k : ℕ) : MemLp
      (fun ω => |brownianIntegralProcess hB f (brownianIntegralGridTime τ k) ω|) 2 P := by
    simpa only [Real.norm_eq_abs] using
      (brownianIntegralProcess_memLp hB f (brownianIntegralGridTime τ k)).norm
  have he : (fun ω => finiteRunningMax
      (fun k => |brownianIntegralProcess hB f (brownianIntegralGridTime τ k) ω|) N) =
      brownianIntegralGridMax hB f τ := funext (fun ω => (brownianIntegralGridMax_eq_running hB f τ ω).symm)
  rw [← he]
  exact finiteRunningMax_memLp h2 N

theorem brownianIntegralProcess_secondMoment_eq_norm (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (T : ℝ≥0) :
    (∫ ω, brownianIntegralProcess hB f T ω ^ 2 ∂P) = ‖brownianTimeCutoff B hBm P T f‖ ^ 2 := by
  calc
    _ = ‖(brownianIntegralProcess_memLp hB f T).toLp (brownianIntegralProcess hB f T)‖ ^ 2 :=
      (TimeTraps.Analysis.memLp_norm_toLp_sq (brownianIntegralProcess_memLp hB f T)).symm
    _ = ‖brownianIntegralUpTo hB T f‖ ^ 2 := by
      change ‖brownianIntegralProcessL2 hB f T‖ ^ 2 = _
      rw [brownianIntegralProcessL2_eq]
    _ = _ := by
      change ‖brownianIntegral hB (brownianTimeCutoff B hBm P T f)‖ ^ 2 = _
      rw [(brownianIntegral hB).norm_map]

theorem brownianIntegralGridMax_le_last (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    (∫ ω, brownianIntegralGridMax hB f τ ω ^ 2 ∂P) ≤
      4 * ∫ ω, brownianIntegralProcess hB f (τ (Fin.last N)) ω ^ 2 ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have h2 (k : ℕ) : MemLp
      (fun ω => |brownianIntegralProcess hB f (brownianIntegralGridTime τ k) ω|) 2 P := by
    simpa only [Real.norm_eq_abs] using
      (brownianIntegralProcess_memLp hB f (brownianIntegralGridTime τ k)).norm
  have h := nonnegative_submartingale_maximal_L2
    (martingale_abs_submartingale (brownianIntegralProcess_grid_martingale hB f τ hτ))
    (fun _ _ => abs_nonneg _) h2 N
  have he : brownianIntegralGridTime τ N = τ (Fin.last N) :=
    brownianIntegralGridTime_at_fin τ (Fin.last N)
  simpa only [brownianIntegralGridMax_eq_running, he, sq_abs] using h

theorem brownianIntegralGridMax_le_norm (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (T : ℝ≥0) (hT : τ (Fin.last N) ≤ T) :
    (∫ ω, brownianIntegralGridMax hB f τ ω ^ 2 ∂P) ≤
      4 * ‖brownianTimeCutoff B hBm P T f‖ ^ 2 := by
  have h := brownianIntegralGridMax_le_last hB f τ hτ
  rw [brownianIntegralProcess_secondMoment_eq_norm] at h
  have hn : ‖brownianTimeCutoff B hBm P (τ (Fin.last N)) f‖ ≤
      ‖brownianTimeCutoff B hBm P T f‖ := by
    calc
      _ = ‖brownianTimeCutoff B hBm P (τ (Fin.last N)) (brownianTimeCutoff B hBm P T f)‖ :=
        congrArg norm (brownianTimeCutoff_of_le hT f).symm
      _ ≤ _ := brownianTimeCutoff_norm_le _ _
  exact h.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn) (by norm_num))

theorem brownianIntegralGridMax_le_secondMoment (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (T : ℝ≥0) (hT : τ (Fin.last N) ≤ T) :
    (∫ ω, brownianIntegralGridMax hB f τ ω ^ 2 ∂P) ≤
      4 * ∫ ω, brownianIntegralProcess hB f T ω ^ 2 ∂P := by
  rw [brownianIntegralProcess_secondMoment_eq_norm]
  exact brownianIntegralGridMax_le_norm hB f τ hτ T hT

theorem brownianStochasticIntegralGridMax_le_norm (f : BrownianIntegrand)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (T : ℝ≥0)
    (hT : τ (Fin.last N) ≤ T) :
    (∫ ω, brownianIntegralGridMax brownianDyadicPath_isPreBrownianReal f τ ω ^ 2
      ∂brownianDyadicMeasure) ≤
      4 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T f‖ ^ 2 :=
  brownianIntegralGridMax_le_norm brownianDyadicPath_isPreBrownianReal f τ hτ T hT

end TimeTraps.Probability
