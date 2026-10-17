module

public import TimeTraps.Probability.BrownianWeightedQuadraticPartition

@[expose] public section

/-! Uniformly bounded signed raw-left-adapted coefficients give the
finite estimate 2 M² Σ(Δt)². Boundedness may hold almost everywhere. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianBoundedCoefficient_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (s : ℝ≥0) {ξ : Ω → ℝ} (M : ℝ≥0)
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hb : ∀ᵐ ω ∂P, |ξ ω| ≤ M.val) : MemLp ξ 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact MemLp.of_bound ((hξ.mono ((brownianNaturalFiltration B hBm).le s)).aestronglyMeasurable)
    M.val (by simpa only [Real.norm_eq_abs] using hb)

theorem brownianBoundedCoefficient_secondMoment (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (s : ℝ≥0) {ξ : Ω → ℝ} (M : ℝ≥0)
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hb : ∀ᵐ ω ∂P, |ξ ω| ≤ M.val) : (∫ ω, ξ ω ^ 2 ∂P) ≤ M.val ^ 2 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hi := (brownianBoundedCoefficient_memLp hB hBm s M hξ hb).integrable_sq
  calc
    _ ≤ ∫ _ : Ω, M.val ^ 2 ∂P := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hb] with ω hω
      have hpair := abs_le.mp hω
      nlinarith [hpair.1, hpair.2]
    _ = _ := by simp

theorem brownianBoundedQuadraticSum_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (M : ℝ≥0) (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ M.val) :
    MemLp (brownianWeightedQuadraticSum B τ ξ) 2 P :=
  brownianWeightedQuadraticSum_memLp hB hBm τ hτ ξ hξ
    (fun i => brownianBoundedCoefficient_memLp hB hBm _ M (hξ i) (hb i))

theorem brownianBoundedQuadraticSum_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (M : ℝ≥0) (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ M.val) :
    (∫ ω, brownianWeightedQuadraticSum B τ ξ ω ∂P) = 0 :=
  brownianWeightedQuadraticSum_mean hB hBm τ hτ ξ hξ
    (fun i => brownianBoundedCoefficient_memLp hB hBm _ M (hξ i) (hb i))

theorem brownianBoundedQuadraticSum_secondMoment_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (M : ℝ≥0) (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ M.val) :
    (∫ ω, brownianWeightedQuadraticSum B τ ξ ω ^ 2 ∂P) ≤
      2 * M.val ^ 2 * ∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val) ^ 2 := by
  rw [brownianWeightedQuadraticSum_secondMoment hB hBm τ hτ ξ hξ
    (fun i => brownianBoundedCoefficient_memLp hB hBm _ M (hξ i) (hb i))]
  calc
    _ ≤ ∑ i : Fin N, 2 * ((τ i.succ).val - (τ i.castSucc).val) ^ 2 * M.val ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (brownianBoundedCoefficient_secondMoment hB hBm _ M (hξ i) (hb i))
        (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

noncomputable def brownianWeightedQuadraticSumL2 (B : ℝ≥0 → Ω → ℝ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ)
    (hSum : MemLp (brownianWeightedQuadraticSum B τ ξ) 2 P) : Lp ℝ 2 P :=
  hSum.toLp (brownianWeightedQuadraticSum B τ ξ)

theorem brownianWeightedQuadraticSumL2_coe (B : ℝ≥0 → Ω → ℝ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ)
    (hSum : MemLp (brownianWeightedQuadraticSum B τ ξ) 2 P) :
    brownianWeightedQuadraticSumL2 B τ ξ hSum =ᵐ[P] brownianWeightedQuadraticSum B τ ξ :=
  hSum.coeFn_toLp

theorem brownianWeightedQuadraticSumL2_norm_sq (B : ℝ≥0 → Ω → ℝ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ξ : Fin N → Ω → ℝ)
    (hSum : MemLp (brownianWeightedQuadraticSum B τ ξ) 2 P) :
    ‖brownianWeightedQuadraticSumL2 B τ ξ hSum‖ ^ 2 =
      ∫ ω, brownianWeightedQuadraticSum B τ ξ ω ^ 2 ∂P :=
  TimeTraps.Analysis.memLp_norm_toLp_sq hSum

theorem brownianBoundedQuadraticSumL2_norm_sq_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ)
    (ξ : Fin N → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (τ i.castSucc)] (ξ i))
    (M : ℝ≥0) (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ M.val)
    (hSum : MemLp (brownianWeightedQuadraticSum B τ ξ) 2 P) :
    ‖brownianWeightedQuadraticSumL2 B τ ξ hSum‖ ^ 2 ≤
      2 * M.val ^ 2 * ∑ i : Fin N, ((τ i.succ).val - (τ i.castSucc).val) ^ 2 := by
  rw [brownianWeightedQuadraticSumL2_norm_sq]
  exact brownianBoundedQuadraticSum_secondMoment_le hB hBm τ hτ ξ hξ M hb

end TimeTraps.Probability
