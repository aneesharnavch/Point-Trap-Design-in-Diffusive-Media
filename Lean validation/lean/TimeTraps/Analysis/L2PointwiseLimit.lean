module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! An actual pointwise limit is identified with a norm limit in L2 by
an almost-everywhere convergent subsequence. No measurability or
integrability assumption is imposed on the initially unknown limit. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter
open scoped Topology

theorem real_L2_eq_ae_of_pointwise_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (U : ℕ → Lp ℝ 2 P) (Y : Lp ℝ 2 P) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hcoe : ∀ n, U n =ᵐ[P] f n) (hlim : Tendsto U atTop (𝓝 Y))
    (hpoint : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) : Y =ᵐ[P] g := by
  obtain ⟨b, hb, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hall : ∀ᵐ ω ∂P, ∀ n, U n ω = f n ω := ae_all_iff.mpr hcoe
  filter_upwards [hsub, hpoint, hall] with ω hs hp he
  have hp' := hp.comp hb.tendsto_atTop
  have hs' : Tendsto (fun n => f (b n) ω) atTop (𝓝 (Y ω)) := by
    simpa only [he] using hs
  exact tendsto_nhds_unique hs' hp'

end TimeTraps.Analysis
