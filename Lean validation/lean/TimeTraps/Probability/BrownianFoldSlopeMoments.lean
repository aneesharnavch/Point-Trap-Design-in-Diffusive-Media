module

public import TimeTraps.Probability.BrownianFoldSlopeGlobal
public import TimeTraps.Probability.BrownianFoldSlopeUnit
public import TimeTraps.Probability.BrownianIntegralMean

@[expose] public section

/-! The constructed normalized fold integral has mean zero and covariance
min(s,t). These identities follow from the actual integral pairing and
the product-almost-everywhere unit slope. They are moment identities;
Gaussian finite-dimensional laws are not inferred from them. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldSlopeProcess_pairing_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (s t : ℝ≥0) :
    (fun p => brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) s p *
      brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) t p)
      =ᵐ[(volume : Measure ℝ).prod P] (fun p => brownianIntervalIndicator 0 (min s t) p.1) := by
  filter_upwards [brownianFoldSlope_square_prod_ae hB hjoint L hL x hσ s] with p hp
  have hm : p.1 ∈ Ioc (0 : ℝ) (min s t).val ↔
      p.1 ∈ Ioc (0 : ℝ) s.val ∧ p.1 ∈ Ioc (0 : ℝ) t.val := by
    change (0 < p.1 ∧ p.1 ≤ min s.val t.val) ↔ _
    simp only [mem_Ioc, le_min_iff]
    tauto
  change brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) s p *
    brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) t p =
      (Ioc (0 : ℝ) (min s t).val).indicator (fun _ => 1) p.1
  by_cases hs : p.1 ∈ Ioc (0 : ℝ) s.val
  · by_cases ht : p.1 ∈ Ioc (0 : ℝ) t.val
    · simpa only [brownianBoundedProcess, brownianSquareProcess,
        Set.indicator_of_mem hs, Set.indicator_of_mem ht,
        Set.indicator_of_mem (hm.mpr ⟨hs, ht⟩), one_mul, ← pow_two] using hp hs
    · simp only [brownianBoundedProcess, brownianSquareProcess, Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (fun h => ht (hm.mp h).2), zero_mul, mul_zero]
  · simp only [brownianBoundedProcess, brownianSquareProcess, Set.indicator_of_notMem hs,
      Set.indicator_of_notMem (fun h => hs (hm.mp h).1), zero_mul]

theorem brownianFoldSlopeIntegral_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    (∫ ω, brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ t ω ∂P) = 0 :=
  brownianIntegral_mean hB _

theorem brownianFoldSlopeIntegral_pairing (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (s t : ℝ≥0) :
    (∫ ω, brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ s ω *
      brownianFoldSlopeIntegral hB hBm hjoint L hL x hσ t ω ∂P) = (min s t).val := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  calc
    _ = ∫ p, (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ s :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) p *
      (brownianFoldSlopeIntegrand hB hBm hjoint L hL x hσ t :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ∂volume.prod P :=
      brownianIntegral_pairing hB _ _
    _ = ∫ p, brownianIntervalIndicator 0 (min s t) p.1 * (1 : ℝ) ∂volume.prod P := by
      apply integral_congr_ae
      filter_upwards [brownianFoldSlopeIntegrand_coe hB hBm hjoint L hL x hσ s,
        brownianFoldSlopeIntegrand_coe hB hBm hjoint L hL x hσ t,
        brownianFoldSlopeProcess_pairing_ae hB hjoint L hL x hσ s t] with p hs ht hp
      rw [hs, ht, hp, mul_one]
    _ = (∫ r, brownianIntervalIndicator 0 (min s t) r) * (∫ _ : Ω, (1 : ℝ) ∂P) :=
      integral_prod_mul (μ := volume) (ν := P) (L := ℝ) _ (fun _ : Ω => (1 : ℝ))
    _ = _ := by
      rw [brownianIntervalIndicator_integral]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      change max ((min s t).val - 0) 0 = (min s t).val
      rw [sub_zero]
      exact max_eq_left (min s t).coe_nonneg

theorem brownianFoldSlopeGlobalPath_mean (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    (∫ ω, brownianFoldSlopeGlobalPath L hL x hσ t ω ∂brownianDyadicMeasure) = 0 := by
  rw [integral_congr_ae (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t)]
  exact brownianFoldSlopeIntegral_mean brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ t

theorem brownianFoldSlopeGlobalPath_pairing (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (s t : ℝ≥0) :
    (∫ ω, brownianFoldSlopeGlobalPath L hL x hσ s ω *
      brownianFoldSlopeGlobalPath L hL x hσ t ω ∂brownianDyadicMeasure) = (min s t).val := by
  calc
    _ = ∫ ω, brownianDyadicFoldSlopeIntegral L hL x hσ s ω *
        brownianDyadicFoldSlopeIntegral L hL x hσ t ω ∂brownianDyadicMeasure := by
      apply integral_congr_ae
      filter_upwards [brownianFoldSlopeGlobalPath_integral_ae L hL x hσ s,
        brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t] with ω hs ht
      rw [hs, ht]
    _ = _ := brownianFoldSlopeIntegral_pairing brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ s t

theorem brownianFoldSlopeGlobalPath_second_moment (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    (∫ ω, brownianFoldSlopeGlobalPath L hL x hσ t ω ^ 2 ∂brownianDyadicMeasure) = t.val := by
  simpa only [pow_two, min_self] using brownianFoldSlopeGlobalPath_pairing L hL x hσ t t

end TimeTraps.Probability
