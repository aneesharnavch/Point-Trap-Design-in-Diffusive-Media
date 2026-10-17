module

public import TimeTraps.Probability.BrownianPredictableSignFinite

@[expose] public section

/-! Actual Gaussian laws of finite predictable unit-sign transforms,
deduced from their characteristic functions. The weighted version gives
all deterministic finite-dimensional linear-combination laws. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianPredictableSignVariance {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (c : Fin N → ℝ) : ℝ≥0 :=
  ⟨∑ i : Fin N, c i ^ 2 * ((τ i.succ).val - (τ i.castSucc).val),
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sub_nonneg.mpr
      (show (τ i.castSucc).val ≤ (τ i.succ).val from hτ (Fin.castSucc_le_succ i))))⟩

theorem brownian_predictable_sign_weighted_hasLaw (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hunit : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| = 1) (c : Fin N → ℝ) :
    HasLaw (brownianStepIntegral B τ (fun i ω => c i * ξ i ω))
      (gaussianReal 0 (brownianPredictableSignVariance τ hτ c)) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hXm : Measurable (brownianStepIntegral B τ (fun i ω => c i * ξ i ω)) :=
    ((brownianStepIntegral_stronglyMeasurable hBm τ hτ (fun i ω => c i * ξ i ω)
      (fun i => (hξ i).const_mul (c i))).mono
        ((brownianNaturalFiltration B hBm).le (τ (Fin.last N)))).measurable
  refine ⟨hXm.aemeasurable, ?_⟩
  apply Measure.ext_of_charFun
  funext u
  calc
    _ = ∫ ω, brownianRealChar u (brownianStepIntegral B τ (fun i ω => c i * ξ i ω) ω) ∂P := by
      rw [charFun_apply_real, integral_map hXm.aemeasurable (by fun_prop)]
      simp only [brownianRealChar, Complex.ofReal_mul]
    _ = Complex.exp (-((∑ i : Fin N, c i ^ 2 * ((τ i.succ).val - (τ i.castSucc).val) : ℝ) : ℂ) *
        (u : ℂ) ^ 2 / 2) := brownian_predictable_sign_finite_char hB hBm τ hτ ξ hξ hunit c u
    _ = _ := by
      rw [charFun_gaussianReal]
      simp only [brownianPredictableSignVariance, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub,
        neg_mul, neg_div]
      rfl

theorem brownianPredictableSignVariance_one {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    brownianPredictableSignVariance τ hτ (fun _ => 1) = τ (Fin.last N) - τ 0 := by
  have hv : (∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val)) =
      (τ (Fin.last N)).val - (τ 0).val := by
    rw [Finset.sum_sub_distrib]
    have h₁ := Fin.sum_univ_succ (fun i : Fin (N + 1) => (τ i).val)
    have h₂ := Fin.sum_univ_castSucc (fun i : Fin (N + 1) => (τ i).val)
    linarith
  apply NNReal.eq
  change (∑ i : Fin N, (1 : ℝ) ^ 2 * ((τ i.succ).val - (τ i.castSucc).val)) = _
  simp only [one_pow, one_mul, hv, NNReal.coe_sub (hτ (Fin.zero_le _))]
  rfl

theorem brownian_predictable_sign_hasLaw (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (hunit : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| = 1) :
    HasLaw (brownianStepIntegral B τ ξ) (gaussianReal 0 (τ (Fin.last N) - τ 0)) P := by
  have he := brownian_predictable_sign_weighted_hasLaw hB hBm τ hτ ξ hξ hunit (fun _ => 1)
  simpa only [one_mul, brownianPredictableSignVariance_one] using he

end TimeTraps.Probability

end
