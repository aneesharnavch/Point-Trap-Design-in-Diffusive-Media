module

public import TimeTraps.Probability.ContinuousMartingaleMaximal

@[expose] public section

/-! A uniformly small continuous correction to a martingale yields a
compact-path mean-square bound for the original process. This is the
maximal estimate needed for potential approximations of local time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {M : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

theorem continuousMartingale_compact_error [IsProbabilityMeasure μ] (hM : Martingale M 𝓕 μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (T : ℝ≥0)
    (F Q : Ω → C(Icc (0 : ℝ≥0) T, ℝ)) (hF2 : MemLp F 2 μ)
    (hQm : AEStronglyMeasurable Q μ) {ε : ℝ}
    (hQ : ∀ᵐ ω ∂μ, ‖Q ω‖ ≤ ε)
    (hMval : ∀ t : Icc (0 : ℝ≥0) T, (fun ω => (F ω + Q ω) t) =ᵐ[μ] M t.val) :
    (∫ ω, ‖F ω‖ ^ 2 ∂μ) ≤ 8 * ∫ ω, M T ω ^ 2 ∂μ + 2 * ε ^ 2 := by
  have hmax := continuousMartingale_compact_maximal hM hM2 T (fun ω => F ω + Q ω)
    (hF2.aestronglyMeasurable.add hQm) hMval
  have hbound : ∀ᵐ ω ∂μ, ‖F ω‖ ^ 2 ≤ 2 * ‖F ω + Q ω‖ ^ 2 + 2 * ε ^ 2 := by
    filter_upwards [hQ] with ω hω
    have htri : ‖F ω‖ ≤ ‖F ω + Q ω‖ + ε := by
      calc
        _ = ‖(F ω + Q ω) - Q ω‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖F ω + Q ω‖ + ‖Q ω‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add le_rfl hω
    nlinarith [norm_nonneg (F ω), norm_nonneg (F ω + Q ω), sq_nonneg (‖F ω + Q ω‖ - ε)]
  have hi := integral_mono_ae hF2.norm.integrable_sq
    ((hmax.1.norm.integrable_sq.const_mul 2).add (integrable_const (2 * ε ^ 2))) hbound
  simp only [Pi.add_apply] at hi
  rw [integral_add (hmax.1.norm.integrable_sq.const_mul 2) (integrable_const (2 * ε ^ 2)),
    integral_const_mul] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  linarith [hmax.2]

end TimeTraps.Probability
