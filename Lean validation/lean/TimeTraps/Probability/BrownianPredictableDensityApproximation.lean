module

public import TimeTraps.Probability.BrownianPredictableDensityIndicator
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

@[expose] public section

/-! Predictable simple approximants converge pointwise with a bound by
twice the target norm. Their finite-horizon cutoffs therefore admit a
single square-integrable dominating function for every L2 process. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter Function
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

noncomputable def brownianPredictableSimpleApprox (hH : IsStronglyPredictable F H) (n : ℕ) :
    @SimpleFunc (ℝ≥0 × Ω) F.predictable ℝ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact SimpleFunc.approxOn (uncurry H) hH.measurable univ 0 (mem_univ 0) n

theorem brownianPredictableSimpleApprox_bound (hH : IsStronglyPredictable F H)
    (n : ℕ) (p : ℝ≥0 × Ω) :
    |brownianPredictableSimpleApprox hH n p| ≤ 2 * |H p.1 p.2| := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have h := SimpleFunc.norm_approxOn_zero_le hH.measurable (mem_univ (0 : ℝ)) p n
  simpa only [brownianPredictableSimpleApprox, Real.norm_eq_abs, Function.uncurry,
    two_mul] using h

theorem brownianPredictableSimpleApprox_tendsto (hH : IsStronglyPredictable F H)
    (p : ℝ≥0 × Ω) :
    Tendsto (fun n => brownianPredictableSimpleApprox hH n p) atTop (𝓝 (H p.1 p.2)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact SimpleFunc.tendsto_approxOn (x := p) hH.measurable (mem_univ (0 : ℝ))
    (by simp only [closure_univ, mem_univ])

theorem brownianPredictableSimpleApprox_cutoff_bound (hH : IsStronglyPredictable F H)
    (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    |brownianSquareProcess (fun t ω => brownianPredictableSimpleApprox hH n (t, ω)) T p| ≤
      2 * |brownianSquareProcess H T p| := by
  by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
  · simpa only [brownianSquareProcess, indicator_of_mem ht, one_mul] using
      brownianPredictableSimpleApprox_bound hH n (p.1.toNNReal, p.2)
  · simp only [brownianSquareProcess, indicator_of_notMem ht, zero_mul, abs_zero, mul_zero,
      le_refl]

theorem brownianPredictableSimpleApprox_cutoff_tendsto (hH : IsStronglyPredictable F H)
    (T : ℝ≥0) (p : ℝ × Ω) :
    Tendsto (fun n => brownianSquareProcess
      (fun t ω => brownianPredictableSimpleApprox hH n (t, ω)) T p)
      atTop (𝓝 (brownianSquareProcess H T p)) := by
  exact (brownianPredictableSimpleApprox_tendsto hH (p.1.toNNReal, p.2)).const_mul
    ((Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1)

end TimeTraps.Probability
