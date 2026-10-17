module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Nonnegativity passes to an actual L² limit by an almost-everywhere
convergent subsequence. No finite-measure hypothesis is required. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter
open scoped Topology

theorem ae_nonnegative_of_L2_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : ℕ → Lp ℝ 2 P) (Y : Lp ℝ 2 P) (hlim : Tendsto S atTop (𝓝 Y))
    (hS : ∀ n, ∀ᵐ ω ∂P, 0 ≤ S n ω) : ∀ᵐ ω ∂P, 0 ≤ Y ω := by
  obtain ⟨a, _, ha⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hn : ∀ᵐ ω ∂P, ∀ n, 0 ≤ S n ω := ae_all_iff.mpr hS
  filter_upwards [ha, hn] with ω hω hnω
  exact ge_of_tendsto hω (Eventually.of_forall fun n => hnω (a n))

end TimeTraps.Analysis
