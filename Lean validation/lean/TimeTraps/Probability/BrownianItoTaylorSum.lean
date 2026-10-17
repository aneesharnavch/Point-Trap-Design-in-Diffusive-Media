module

public import TimeTraps.Probability.BrownianItoTaylorIncrement

@[expose] public section

/-! Absolute first-moment control of the full finite Taylor error.
The sum is the actual pathwise remainder over the chosen partition. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℝ → ℝ}

noncomputable def brownianItoTaylorSum (B : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin N, brownianItoTaylorIncrement B F (τ i.castSucc) (τ i.succ) ω

theorem brownianItoTaylorSum_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) :
    Integrable (brownianItoTaylorSum B F τ) P :=
  integrable_finsetSum _ (fun i _ =>
    brownianItoTaylorIncrement_integrable hB hBm hF hb (τ i.castSucc) (τ i.succ))

theorem brownianItoTaylorSum_mean_abs_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M : ℝ} (hb : ∀ z, |iteratedDeriv 3 F z| ≤ M) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) :
    (∫ ω, |brownianItoTaylorSum B F τ ω| ∂P) ≤
      ∑ i : Fin N, (M / 6) * (Real.sqrt 3 * |(τ i.succ).val - (τ i.castSucc).val| *
        Real.sqrt |(τ i.succ).val - (τ i.castSucc).val|) := by
  calc
    _ ≤ ∫ ω, ∑ i : Fin N,
        |brownianItoTaylorIncrement B F (τ i.castSucc) (τ i.succ) ω| ∂P := by
      apply integral_mono_ae (brownianItoTaylorSum_integrable hB hBm hF hb τ).abs
        (integrable_finsetSum _ (fun i _ =>
          (brownianItoTaylorIncrement_integrable hB hBm hF hb _ _).abs))
      exact Filter.Eventually.of_forall (fun ω => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i : Fin N, ∫ ω,
        |brownianItoTaylorIncrement B F (τ i.castSucc) (τ i.succ) ω| ∂P :=
      integral_finsetSum _ (fun i _ =>
        (brownianItoTaylorIncrement_integrable hB hBm hF hb _ _).abs)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => brownianItoTaylorIncrement_mean_abs_le hB hBm hF hb _ _)

noncomputable def brownianItoTaylorSumL1 (B : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (h : Integrable (brownianItoTaylorSum B F τ) P) :
    Lp ℝ 1 P := h.toL1 (brownianItoTaylorSum B F τ)

theorem brownianItoTaylorSumL1_coe {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (h : Integrable (brownianItoTaylorSum B F τ) P) :
    brownianItoTaylorSumL1 B F τ h =ᵐ[P] brownianItoTaylorSum B F τ := h.coeFn_toL1

theorem brownianItoTaylorSumL1_norm {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (h : Integrable (brownianItoTaylorSum B F τ) P) :
    ‖brownianItoTaylorSumL1 B F τ h‖ = ∫ ω, |brownianItoTaylorSum B F τ ω| ∂P := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [brownianItoTaylorSumL1_coe τ h] with ω he
  rw [Real.norm_eq_abs, he]

end TimeTraps.Probability
