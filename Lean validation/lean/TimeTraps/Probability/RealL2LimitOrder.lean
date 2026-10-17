module

public import TimeTraps.Analysis.IntegralCauchySchwarz
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Positivity, order, and expectation pass through genuine real L2
limits. Positivity uses an almost-everywhere convergent subsequence;
expectation is the Hilbert pairing with the integrable constant one. -/

namespace TimeTraps.Probability

open MeasureTheory Filter TimeTraps.Analysis
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem realL2_integral_eq_inner_one [IsFiniteMeasure μ] (u : Lp ℝ 2 μ) :
    (∫ ω, u ω ∂μ) = inner ℝ u ((memLp_const (1 : ℝ)).toLp (fun _ : Ω => 1)) := by
  have h := memLp_inner_toLp_eq_integral_mul (Lp.memLp u) (memLp_const (1 : ℝ))
  simpa only [Lp.toLp_coeFn, mul_one] using h.symm

theorem realL2_integral_continuous [IsFiniteMeasure μ] :
    Continuous (fun u : Lp ℝ 2 μ => ∫ ω, u ω ∂μ) := by
  simp_rw [realL2_integral_eq_inner_one]
  exact continuous_id.inner continuous_const

theorem realL2_limit_nonneg_ae {u : ℕ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ}
    (hu : Tendsto u atTop (𝓝 v)) (hn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ u n ω) :
    ∀ᵐ ω ∂μ, 0 ≤ v ω := by
  obtain ⟨s, _, hs⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  filter_upwards [hs, ae_all_iff.mpr hn] with ω hω hnω
  exact ge_of_tendsto hω (Eventually.of_forall (fun n => hnω (s n)))

theorem realL2_limit_le_ae {u v : ℕ → Lp ℝ 2 μ} {f g : Lp ℝ 2 μ}
    (hu : Tendsto u atTop (𝓝 f)) (hv : Tendsto v atTop (𝓝 g))
    (hn : ∀ n, ∀ᵐ ω ∂μ, u n ω ≤ v n ω) : ∀ᵐ ω ∂μ, f ω ≤ g ω := by
  have hnon : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ (v n - u n) ω := by
    intro n
    filter_upwards [hn n, Lp.coeFn_sub (v n) (u n)] with ω hω he
    simpa only [he, Pi.sub_apply, sub_nonneg] using hω
  have h := realL2_limit_nonneg_ae (hv.sub hu) hnon
  filter_upwards [h, Lp.coeFn_sub g f] with ω hω he
  simpa only [he, Pi.sub_apply, sub_nonneg] using hω

end TimeTraps.Probability
