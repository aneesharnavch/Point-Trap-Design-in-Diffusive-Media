module

public import TimeTraps.Probability.BrownianPredictableSignPastStep

@[expose] public section

/-! Finite predictable unit-sign transforms retain their characteristic
law against any integrable complex multiplier measurable before the
grid starts. This keeps the original Brownian filtration explicit. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_predictable_sign_past_finite_char (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {Z : Ω → ℂ} (hZi : Integrable Z P)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hunit : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| = 1) (c : Fin N → ℝ)
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm (τ 0)] Z) (u : ℝ) :
    (∫ ω, Z ω * brownianRealChar u (brownianStepIntegral B τ (fun i ω => c i * ξ i ω) ω) ∂P) =
      (∫ ω, Z ω ∂P) *
        Complex.exp (-((∑ i : Fin N, c i ^ 2 * ((τ i.succ).val - (τ i.castSucc).val) : ℝ) : ℂ) *
          (u : ℂ) ^ 2 / 2) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  induction N with
  | zero => simp [brownianStepIntegral, brownianRealChar]
  | succ N ih =>
      let τ₀ : Fin (N + 1) → ℝ≥0 := fun i => τ i.castSucc
      let ξ₀ : Fin N → Ω → ℝ := fun i => ξ i.castSucc
      let c₀ : Fin N → ℝ := fun i => c i.castSucc
      have hτ₀ : Monotone τ₀ := hτ.comp Fin.strictMono_castSucc.monotone
      have hξ₀ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ₀ i.castSucc)] (ξ₀ i) :=
        fun i => hξ i.castSucc
      have hu₀ : ∀ i, ∀ᵐ ω ∂P, |ξ₀ i ω| = 1 := fun i => hunit i.castSucc
      have hZ₀ : StronglyMeasurable[brownianNaturalFiltration B hBm (τ₀ 0)] Z := hZ
      let Y : Ω → ℝ := brownianStepIntegral B τ₀ (fun i ω => c₀ i * ξ₀ i ω)
      have hY : StronglyMeasurable[brownianNaturalFiltration B hBm (τ (Fin.last N).castSucc)] Y :=
        brownianStepIntegral_stronglyMeasurable hBm τ₀ hτ₀ (fun i ω => c₀ i * ξ₀ i ω)
          (fun i => (hξ₀ i).const_mul (c₀ i))
      let F : Ω → ℂ := fun ω => Z ω * brownianRealChar u (Y ω)
      have hF : StronglyMeasurable[brownianNaturalFiltration B hBm (τ (Fin.last N).castSucc)] F :=
        (hZ.mono ((brownianNaturalFiltration B hBm).mono (hτ (Fin.zero_le _)))).mul
          (((brownianRealChar_measurable u).comp hY.measurable).stronglyMeasurable)
      have hFi : Integrable F P := brownianRealChar_mul_integrable hZi
        (hY.mono ((brownianNaturalFiltration B hBm).le _)).measurable u
      have hstep := brownian_predictable_sign_past_step hB hBm
        (hτ (Fin.castSucc_le_succ (Fin.last N))) hF hFi (hξ (Fin.last N)) (hunit (Fin.last N)) u (c (Fin.last N))
      have he : (fun ω => brownianStepIntegral B τ (fun i ω => c i * ξ i ω) ω) =
          fun ω => Y ω + c (Fin.last N) * (ξ (Fin.last N) ω *
            (B (τ (Fin.last N).succ) ω - B (τ (Fin.last N).castSucc) ω)) := by
        funext ω
        rw [brownianStepIntegral, Fin.sum_univ_castSucc]
        change (∑ i : Fin N, c i.castSucc * ξ i.castSucc ω *
            (B (τ i.castSucc.succ) ω - B (τ i.castSucc.castSucc) ω)) + _ = _
        simp only [Y, brownianStepIntegral, τ₀, ξ₀, c₀, Fin.succ_castSucc]
        ring
      have hfull : (fun ω => Z ω * brownianRealChar u (brownianStepIntegral B τ (fun i ω => c i * ξ i ω) ω)) =
          fun ω => F ω * brownianRealChar u (c (Fin.last N) * (ξ (Fin.last N) ω *
            (B (τ (Fin.last N).succ) ω - B (τ (Fin.last N).castSucc) ω))) := by
        funext ω
        rw [congrFun he ω, brownianRealChar_add]
        exact (mul_assoc _ _ _).symm
      have hv : (∑ i : Fin (N + 1), c i ^ 2 * ((τ i.succ).val - (τ i.castSucc).val)) =
          (∑ i : Fin N, c₀ i ^ 2 * ((τ₀ i.succ).val - (τ₀ i.castSucc).val)) +
            c (Fin.last N) ^ 2 * ((τ (Fin.last N).succ).val - (τ (Fin.last N).castSucc).val) := by
        rw [Fin.sum_univ_castSucc]
        simp only [τ₀, c₀, Fin.succ_castSucc]
      rw [hfull, hstep]
      change (∫ ω, Z ω * brownianRealChar u (brownianStepIntegral B τ₀ (fun i ω => c₀ i * ξ₀ i ω) ω) ∂P) * _ = _
      rw [ih τ₀ hτ₀ ξ₀ hξ₀ hu₀ c₀ hZ₀, mul_assoc, ← Complex.exp_add, hv]
      congr 2
      push_cast
      ring

theorem brownian_predictable_sign_earlier_char (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {Z : Ω → ℂ} (hZi : Integrable Z P)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hunit : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| = 1) (c : Fin N → ℝ)
    {s : ℝ≥0} (hs : s ≤ τ 0) (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z) (u : ℝ) :
    (∫ ω, Z ω * brownianRealChar u (brownianStepIntegral B τ (fun i ω => c i * ξ i ω) ω) ∂P) =
      (∫ ω, Z ω ∂P) *
        Complex.exp (-((∑ i : Fin N, c i ^ 2 * ((τ i.succ).val - (τ i.castSucc).val) : ℝ) : ℂ) *
          (u : ℂ) ^ 2 / 2) :=
  brownian_predictable_sign_past_finite_char hB hBm hZi τ hτ ξ hξ hunit c
    (hZ.mono ((brownianNaturalFiltration B hBm).mono hs)) u

end TimeTraps.Probability
