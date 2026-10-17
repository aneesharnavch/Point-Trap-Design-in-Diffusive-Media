module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Identification of an actual almost-everywhere limit from an L2
principal term and an L1 remainder. Nested almost-sure subsequences use
only convergence in measure; the unknown function needs no integrability
or measurability premise, and the measure need not be finite. -/

namespace TimeTraps.Probability

open MeasureTheory Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem ae_eq_lp_limit_of_remainder (S : ℕ → Lp ℝ 2 P) (Y : Lp ℝ 2 P)
    (R : ℕ → Lp ℝ 1 P) (H : Ω → ℝ)
    (hS : Tendsto S atTop (𝓝 Y)) (hR : Tendsto R atTop (𝓝 0))
    (hH : ∀ n, H =ᵐ[P] fun ω => S n ω + R n ω) : H =ᵐ[P] Y := by
  obtain ⟨a, ha, hSa⟩ := (tendstoInMeasure_of_tendsto_Lp hS).exists_seq_tendsto_ae
  have hRa : Tendsto (fun n => R (a n)) atTop (𝓝 0) := hR.comp ha.tendsto_atTop
  obtain ⟨b, hb, hRb⟩ := (tendstoInMeasure_of_tendsto_Lp hRa).exists_seq_tendsto_ae
  have hH_all : ∀ᵐ ω ∂P, ∀ n, H ω = S n ω + R n ω := ae_all_iff.mpr hH
  filter_upwards [hSa, hRb, hH_all, Lp.coeFn_zero ℝ 1 P] with ω hSω hRω hHω hz
  have hS' : Tendsto (fun n => S (a (b n)) ω) atTop (𝓝 (Y ω)) :=
    hSω.comp hb.tendsto_atTop
  have hR' : Tendsto (fun n => R (a (b n)) ω) atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun n => R (a (b n)) ω) atTop (𝓝 ((0 : Lp ℝ 1 P) ω)) at hRω
    rw [hz] at hRω
    exact hRω
  have hsum : Tendsto (fun _ : ℕ => H ω) atTop (𝓝 (Y ω)) := by
    simpa only [← hHω, add_zero] using hS'.add hR'
  exact tendsto_nhds_unique tendsto_const_nhds hsum

end TimeTraps.Probability
