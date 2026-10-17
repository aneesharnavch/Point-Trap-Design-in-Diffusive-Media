module

public import TimeTraps.Probability.ContinuousMartingaleMaximalSample
public import TimeTraps.Probability.BrownianIntegralCompactMaximalTopology
public import TimeTraps.Probability.BrownianIntegralCompactMaximalFatou

@[expose] public section

/-! A continuous real martingale has square-integrable compact-time
supremum, bounded by four times its terminal second moment. Finite
maxima and Fatou prove the claim for the actual continuous version. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace TimeTraps.Analysis
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {M : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

theorem continuousMartingale_compact_maximal [IsFiniteMeasure μ] (hM : Martingale M 𝓕 μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (T : ℝ≥0) (F : Ω → C(Icc (0 : ℝ≥0) T, ℝ))
    (hFm : AEStronglyMeasurable F μ)
    (hF : ∀ t : Icc (0 : ℝ≥0) T, (fun ω => F ω t) =ᵐ[μ] M t.val) :
    MemLp F 2 μ ∧ (∫ ω, ‖F ω‖ ^ 2 ∂μ) ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ := by
  let inst : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, zero_le⟩⟩
  let d := denseSeq (Icc (0 : ℝ≥0) T)
  let τ : ℕ → ℝ≥0 := fun n => (d n).val
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => finiteRunningMax (fun k => |M (τ k) ω|) n)
      atTop (𝓝 ‖F ω‖) := by
    filter_upwards [ae_all_iff.mpr (fun n => hF (d n))] with ω hω
    simpa only [hω, Real.norm_eq_abs] using
      compactPath_runningMax_tendsto (F ω) d (denseRange_denseSeq _)
  have hb : ∀ n, (∫ ω, finiteRunningMax (fun k => |M (τ k) ω|) n ^ 2 ∂μ) ≤
      (2 * ‖(hM2 T).toLp (M T)‖) ^ 2 := by
    intro n
    have h := martingaleSampleMax_second_moment hM hM2 τ T (fun k => (d k).property.2) n
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, memLp_norm_toLp_sq] using h
  have h := compactMaximal_memLp_of_tendsto (by positivity)
    (martingaleSampleMax_memLp hM2 τ) hFm.norm hlim hb
  refine ⟨(memLp_norm_iff hFm).mp h.1, ?_⟩
  simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, memLp_norm_toLp_sq] using h.2

end TimeTraps.Probability
