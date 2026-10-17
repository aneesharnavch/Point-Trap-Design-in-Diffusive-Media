module

public import TimeTraps.Probability.BrownianFoldSlopeIntegrand
public import TimeTraps.Probability.BrownianIntegralTruncation

@[expose] public section

/-! The normalized fold-slope integrands on different horizons agree
under actual product-L² time restriction. The proof uses their raw
representatives, so no global square integrability in time is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldSlopeIntegrand_cutoff (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T t : ℝ≥0) :
    brownianTimeCutoff B hBm P t (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T) =
      brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ (min t T) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [brownianTimeCutoff_coe t (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T),
    brownianFoldSlopeIntegrand_coe hB hBm hjoint L hL x hσ T,
    brownianFoldSlopeIntegrand_coe hB hBm hjoint L hL x hσ (min t T)] with p hcut hT hmin
  rw [hcut, hmin]
  unfold brownianBoundedProcess brownianSquareProcess at hT ⊢
  by_cases ht : p.1 ≤ t.val
  · have hp : p ∈ brownianTimePast t := ht
    rw [indicator_of_mem hp, hT]
    have hle : p.1 ≤ (min t T).val ↔ p.1 ≤ T.val := by
      change p.1 ≤ min t.val T.val ↔ p.1 ≤ T.val
      simp only [le_min_iff, ht, true_and]
    simp only [indicator_apply, mem_Ioc, hle]
  · have hp : p ∉ brownianTimePast t := ht
    rw [indicator_of_notMem hp]
    have hn : p.1 ∉ Ioc (0 : ℝ) (min t T).val := by
      intro h
      exact ht (h.2.trans (min_le_left t.val T.val))
    rw [indicator_of_notMem hn, zero_mul]

theorem brownianFoldSlopeIntegral_upTo (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T t : ℝ≥0) :
    brownianIntegralUpTo hB t (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T) =
      brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ (min t T) := by
  change brownianIntegral hB (brownianTimeCutoff B hBm P t
    (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T)) = _
  rw [brownianFoldSlopeIntegrand_cutoff]
  rfl

theorem brownianFoldSlopeIntegral_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T t : ℝ≥0) :
    P[brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ T | brownianNaturalFiltration B hBm t] =ᵐ[P]
      brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ (min t T) := by
  have h := brownianIntegralUpTo_condExp hB t (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ T)
  rw [brownianFoldSlopeIntegral_upTo] at h
  exact h

theorem brownianFoldSlopeIntegrand_zero (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ 0 = 0 := by
  apply Subtype.ext
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [brownianFoldSlopeIntegrand_coe hB hBm hjoint L hL x hσ 0] with p hp
  rw [hp]
  simp [brownianBoundedProcess, brownianSquareProcess]

theorem brownianFoldSlopeIntegral_zero (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ 0 = 0 := by
  rw [brownianFoldSlopeIntegral, brownianFoldSlopeIntegrand_zero, map_zero]

end TimeTraps.Probability
