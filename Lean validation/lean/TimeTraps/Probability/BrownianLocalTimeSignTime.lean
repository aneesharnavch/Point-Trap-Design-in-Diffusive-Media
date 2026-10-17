module

public import TimeTraps.Probability.BrownianLocalTimeNorm

@[expose] public section

/-! The actual sign stochastic integral has exact Brownian-scale
second moments for its time increments, uniformly over the level.
The proof uses the actual product-L2 integrand and Gaussian atomlessness. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSignProcess_time_sub (B : ℝ≥0 → Ω → ℝ) (a : ℝ)
    {S T : ℝ≥0} (hst : S ≤ T) (p : ℝ × Ω) :
    brownianSignProcess B a T p - brownianSignProcess B a S p =
      brownianIntervalIndicator S T p.1 * Real.sign (B p.1.toNNReal p.2 - a) := by
  change (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * _ -
    (Ioc (0 : ℝ) S.val).indicator (fun _ => 1) p.1 * _ =
      (Ioc S.val T.val).indicator (fun _ => 1) p.1 * _
  have hst' : S.val ≤ T.val := hst
  by_cases hs : p.1 ≤ S.val
  · have hST : p.1 ∉ Ioc S.val T.val := fun h => (not_lt_of_ge hs) h.1
    by_cases hz : 0 < p.1
    · simp only [indicator_of_mem (show p.1 ∈ Ioc (0 : ℝ) T.val from ⟨hz, hs.trans hst'⟩),
        indicator_of_mem (show p.1 ∈ Ioc (0 : ℝ) S.val from ⟨hz, hs⟩),
        indicator_of_notMem hST, one_mul, zero_mul, sub_self]
    · simp only [indicator_of_notMem (show p.1 ∉ Ioc (0 : ℝ) T.val from fun h => hz h.1),
        indicator_of_notMem (show p.1 ∉ Ioc (0 : ℝ) S.val from fun h => hz h.1),
        indicator_of_notMem hST, zero_mul, sub_self]
  · have hS : p.1 ∉ Ioc (0 : ℝ) S.val := fun h => hs h.2
    by_cases ht : p.1 ≤ T.val
    · have hz : 0 < p.1 := S.coe_nonneg.trans_lt (lt_of_not_ge hs)
      simp only [indicator_of_mem (show p.1 ∈ Ioc (0 : ℝ) T.val from ⟨hz, ht⟩),
        indicator_of_mem (show p.1 ∈ Ioc S.val T.val from ⟨lt_of_not_ge hs, ht⟩),
        indicator_of_notMem hS, zero_mul, sub_zero]
    · simp only [indicator_of_notMem (show p.1 ∉ Ioc (0 : ℝ) T.val from fun h => ht h.2),
        indicator_of_notMem (show p.1 ∉ Ioc S.val T.val from fun h => ht h.2),
        indicator_of_notMem hS, zero_mul, sub_zero]

theorem brownianSignIntegral_time_norm_sq_of_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ)
    {S T : ℝ≥0} (hst : S ≤ T) :
    ‖brownianSignIntegral hB hBm hjoint a T - brownianSignIntegral hB hBm hjoint a S‖ ^ 2 =
      T.val - S.val := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let U : brownianIntegralSpace B hBm P := brownianSignIntegrand hB hBm hjoint a T
  let V : brownianIntegralSpace B hBm P := brownianSignIntegrand hB hBm hjoint a S
  let D : Lp ℝ 2 ((volume : Measure ℝ).prod P) := (U : Lp ℝ 2 ((volume : Measure ℝ).prod P)) - (V : Lp ℝ 2 ((volume : Measure ℝ).prod P))
  have hD : D =ᵐ[volume.prod P]
      (fun p => brownianSignProcess B a T p - brownianSignProcess B a S p) := by
    filter_upwards [Lp.coeFn_sub (U : Lp ℝ 2 ((volume : Measure ℝ).prod P)) (V : Lp ℝ 2 ((volume : Measure ℝ).prod P)),
      brownianSignIntegrand_coe hB hBm hjoint a T,
      brownianSignIntegrand_coe hB hBm hjoint a S] with p hd hu hv
    change ((U : Lp ℝ 2 ((volume : Measure ℝ).prod P)) - (V : Lp ℝ 2 ((volume : Measure ℝ).prod P))) p = _
    rw [hd, Pi.sub_apply, hu, hv]
    rfl
  calc
    _ = ‖D‖ ^ 2 := by
      rw [brownianSignIntegral, brownianSignIntegral, ← map_sub, brownianIntegral_norm]
      rfl
    _ = ∫ p, D p ^ 2 ∂volume.prod P := by
      simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp D)
    _ = ∫ p : ℝ × Ω, brownianIntervalIndicator S T p.1 * (1 : ℝ) ∂volume.prod P := by
      apply integral_congr_ae
      filter_upwards [hD, brownian_positive_time_ne_level_prod_ae hB hjoint a T] with p hd hp
      rw [hd, brownianSignProcess_time_sub B a hst]
      change ((Ioc S.val T.val).indicator (fun _ => 1) p.1 * _) ^ 2 =
        (Ioc S.val T.val).indicator (fun _ => 1) p.1 * 1
      by_cases ht : p.1 ∈ Ioc S.val T.val
      · have hz : p.1 ∈ Ioc (0 : ℝ) T.val := ⟨S.coe_nonneg.trans_lt ht.1, ht.2⟩
        simp only [indicator_of_mem ht, one_mul]
        rcases Real.sign_apply_eq_of_ne_zero _ (sub_ne_zero.mpr (hp hz)) with hn | hn <;>
          rw [hn] <;> norm_num
      · simp only [indicator_of_notMem ht, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    _ = (∫ s, brownianIntervalIndicator S T s) * ∫ _ : Ω, (1 : ℝ) ∂P :=
      integral_prod_mul (μ := volume) (ν := P) (L := ℝ) (brownianIntervalIndicator S T) (fun _ => 1)
    _ = T.val - S.val := by
      rw [brownianIntervalIndicator_integral, max_eq_left (sub_nonneg.mpr (show S.val ≤ T.val from hst))]
      simp

theorem brownianSignIntegral_time_norm_sq (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (S T : ℝ≥0) :
    ‖brownianSignIntegral hB hBm hjoint a T - brownianSignIntegral hB hBm hjoint a S‖ ^ 2 =
      |T.val - S.val| := by
  rcases le_total S T with hst | hts
  · rw [brownianSignIntegral_time_norm_sq_of_le hB hBm hjoint a hst,
      abs_of_nonneg (sub_nonneg.mpr (show S.val ≤ T.val from hst))]
  · rw [norm_sub_rev, brownianSignIntegral_time_norm_sq_of_le hB hBm hjoint a hts,
      abs_of_nonpos (sub_nonpos.mpr (show T.val ≤ S.val from hts)), neg_sub]

theorem brownianSignIntegral_time_norm (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (S T : ℝ≥0) :
    ‖brownianSignIntegral hB hBm hjoint a T - brownianSignIntegral hB hBm hjoint a S‖ =
      Real.sqrt |T.val - S.val| := by
  have h := congrArg Real.sqrt (brownianSignIntegral_time_norm_sq hB hBm hjoint a S T)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using h

end TimeTraps.Probability
