module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Limit identification with an L2 principal term and an arbitrary
pathwise convergent remainder. A single almost-sure subsequence suffices;
the unknown functions need no measurability or integrability premise. -/

namespace TimeTraps.Probability

open MeasureTheory Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem ae_eq_lp_limit_of_pathwise_remainder (S : ℕ → Lp ℝ 2 P) (Y : Lp ℝ 2 P)
    (R : ℕ → Ω → ℝ) (r H : Ω → ℝ)
    (hS : Tendsto S atTop (𝓝 Y))
    (hR : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 (r ω)))
    (hH : ∀ n, H =ᵐ[P] fun ω => S n ω + R n ω) :
    H =ᵐ[P] fun ω => Y ω + r ω := by
  obtain ⟨a, ha, hSa⟩ := (tendstoInMeasure_of_tendsto_Lp hS).exists_seq_tendsto_ae
  have hH_all : ∀ᵐ ω ∂P, ∀ n, H ω = S n ω + R n ω := ae_all_iff.mpr hH
  filter_upwards [hSa, hR, hH_all] with ω hSω hRω hHω
  have hRa : Tendsto (fun n => R (a n) ω) atTop (𝓝 (r ω)) := hRω.comp ha.tendsto_atTop
  have hsum : Tendsto (fun _ : ℕ => H ω) atTop (𝓝 (Y ω + r ω)) := by
    simpa only [← hHω] using hSω.add hRa
  exact tendsto_nhds_unique tendsto_const_nhds hsum

end TimeTraps.Probability
