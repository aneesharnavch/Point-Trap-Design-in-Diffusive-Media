module

public import TimeTraps.Probability.ReflectedLocalTimeBandErrorLimit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! A mean-square band limit yields an almost-everywhere convergent
sequence of genuine bands. Only sufficiently narrow-band errors need
be square-integrable; no measurability of the proposed limit is assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped Topology ENNReal

theorem occupationBand_exists_sequence_tendsto_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℝ → Ω → ℝ} {g : Ω → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ h, 0 < h → h < r → MemLp (fun ω => f h ω - g ω) 2 P)
    (hlim : Tendsto (fun h => ∫ ω, (f h ω - g ω) ^ 2 ∂P) (𝓝[>] 0) (𝓝 0)) :
    ∃ u : ℕ → ℝ, (∀ n, 0 < u n ∧ u n < r) ∧ Tendsto u atTop (𝓝 0) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => f (u n) ω) atTop (𝓝 (g ω)) := by
  let u : ℕ → ℝ := fun n => (r / 2) * (1 / ((n : ℝ) + 1))
  have hu (n : ℕ) : 0 < u n ∧ u n < r := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hn).mpr
      simp only [one_mul]
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    constructor
    · dsimp [u]
      positivity
    · have hb := mul_le_mul_of_nonneg_left hle (show 0 ≤ r / 2 by positivity)
      dsimp [u]
      linarith
  have ht : Tendsto u atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r / 2)
  have ht' : Tendsto u atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨ht, Eventually.of_forall (fun n => (hu n).1)⟩
  let F : ℕ → Lp ℝ 2 P := fun n => (hf (u n) (hu n).1 (hu n).2).toLp (fun ω => f (u n) ω - g ω)
  have hsq : Tendsto (fun n => ‖F n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have he (n : ℕ) : ‖F n‖ ^ 2 = ∫ ω, (f (u n) ω - g ω) ^ 2 ∂P :=
      memLp_norm_toLp_sq (hf (u n) (hu n).1 (hu n).2)
    simpa only [he, Function.comp_def] using hlim.comp ht'
  have hF : Tendsto F atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [sub_zero, Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs
  obtain ⟨v, hv, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ ω ∂P, ∀ n, F n ω = f (u n) ω - g ω :=
    ae_all_iff.mpr (fun n => (hf (u n) (hu n).1 (hu n).2).coeFn_toLp)
  refine ⟨u ∘ v, (fun n => hu (v n)), ht.comp hv.tendsto_atTop, ?_⟩
  filter_upwards [hAE, hcoe, Lp.coeFn_zero ℝ 2 P] with ω hω he hz
  have hh : Tendsto (fun n => f (u (v n)) ω - g ω) atTop (𝓝 0) := by
    simpa only [he, hz, Pi.zero_apply] using hω
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hh.add_const (g ω)

end TimeTraps.Probability
