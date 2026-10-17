module

public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! Summable expected squared errors force almost-sure convergence of
the entire sequence. This is an analytic summability argument, with no
selected subsequence or numerical error cutoff in the conclusion. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter
open scoped ENNReal Topology

theorem ae_tendsto_zero_of_summable_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 P)
    (hsum : Summable (fun n => ∫ ω, f n ω ^ 2 ∂P)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
  have he (n : ℕ) : eLpNorm (fun ω => f n ω ^ 2) 1 P =
      ENNReal.ofReal (∫ ω, f n ω ^ 2 ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hf n).integrable_sq]
    simp only [Real.norm_eq_abs, abs_sq]
  have ht : ∑' n, eLpNorm (fun ω => f n ω ^ 2) 1 P ≠ ∞ := by
    simpa only [he] using hsum.tsum_ofReal_ne_top
  have hs := summable_norm_of_tsum_eLpNorm_ne_top (show (1 : ℝ≥0∞) ≤ 1 from le_rfl)
    (fun n => (hf n).integrable_sq.aestronglyMeasurable) ht
  filter_upwards [hs] with ω hω
  have hsq : Tendsto (fun n => f n ω ^ 2) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, abs_sq] using hω.tendsto_atTop_zero
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, sub_zero, Real.norm_eq_abs,
    Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hr

end TimeTraps.Analysis
