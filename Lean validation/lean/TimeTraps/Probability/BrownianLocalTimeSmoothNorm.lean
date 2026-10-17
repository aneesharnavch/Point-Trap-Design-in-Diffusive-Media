module

public import TimeTraps.Probability.BrownianLocalTimeNorm

@[expose] public section

/-! Smooth Tanaka compensations have the same uniform 2 sqrt T L²
bound as their limit. Smooth absolute values are 1-Lipschitz, and their
bounded slopes are compared in the actual integrand space with sign. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianLipschitzDifferenceL2_norm_le (hB : IsPreBrownianReal B P)
    {F : ℝ → ℝ} (hF : LipschitzWith 1 F) (T : ℝ≥0)
    (hF₂ : MemLp (brownianTanakaApproxDifference B F T) 2 P) :
    ‖brownianTanakaApproxDifferenceL2 B F T hF₂‖ ≤ Real.sqrt T.val := by
  have hs : ‖brownianTanakaApproxDifferenceL2 B F T hF₂‖ ^ 2 ≤ T.val := by
    calc
      _ = ∫ ω, brownianTanakaApproxDifference B F T ω ^ 2 ∂P := memLp_norm_toLp_sq hF₂
      _ ≤ ∫ ω, (B T ω - B 0 ω) ^ 2 ∂P := by
        apply integral_mono hF₂.integrable_sq (brownian_increment_integrable_sq hB 0 T)
        intro ω
        have hb : |F (B T ω) - F (B 0 ω)| ≤ |B T ω - B 0 ω| := by
          simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hF.dist_le_mul (B T ω) (B 0 ω)
        simpa only [brownianTanakaApproxDifference, sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hb
      _ = T.val := by simpa using brownian_increment_second_moment hB 0 T
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  exact hs.trans_eq (Real.sq_sqrt T.coe_nonneg).symm

theorem brownianTanakaSmoothIntegral_norm_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    ‖brownianTanakaSmoothIntegral hB hBm hjoint a T n‖ ≤ Real.sqrt T.val := by
  let I := brownianItoIntegrand hB hBm
    (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a)
    (brownianTanakaSmooth_second_bound n a) hjoint T
  let S := brownianSignIntegrand hB hBm hjoint a T
  have hcmp : ‖I‖ ≤ ‖S‖ := by
    change ‖(I : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖ ≤
      ‖(S : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [brownianItoIntegrand_coe hB hBm
      (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a)
      (brownianTanakaSmooth_second_bound n a) hjoint T,
      brownianSignIntegrand_coe hB hBm hjoint a T,
      brownian_positive_time_ne_level_prod_ae hB hjoint a T] with p hi hs hp
    rw [hi, hs]
    simp only [Real.norm_eq_abs]
    by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
    · simp only [indicator_of_mem ht, one_mul]
      rcases Real.sign_apply_eq_of_ne_zero _ (sub_ne_zero.mpr (hp ht)) with hn | hn <;>
        rw [hn] <;>
        simpa only [abs_neg, abs_one] using
          tanakaSmoothShift_first_bound (tanakaSmoothingScale_pos n) a (B p.1.toNNReal p.2)
    · simp only [indicator_of_notMem ht, zero_mul, abs_zero, le_refl]
  calc
    _ = ‖I‖ := (brownianIntegral hB).norm_map I
    _ ≤ ‖S‖ := hcmp
    _ = ‖brownianSignIntegral hB hBm hjoint a T‖ := ((brownianIntegral hB).norm_map S).symm
    _ = _ := brownianSignIntegral_norm hB hBm hjoint a T

theorem brownianTanakaSmoothCompensation_norm_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    ‖brownianTanakaSmoothCompensation hB hBm hjoint a T n‖ ≤ 2 * Real.sqrt T.val := by
  let F := tanakaSmoothShift (tanakaSmoothingScale n) a
  have hF : LipschitzWith 1 F := by
    apply lipschitzWith_of_nnnorm_deriv_le
      ((tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a).differentiable (by norm_num))
    intro x
    change ‖deriv F x‖ ≤ (1 : ℝ)
    simpa only [Real.norm_eq_abs] using tanakaSmoothShift_first_bound (tanakaSmoothingScale_pos n) a x
  let hM := brownianTanakaApproxDifference_memLp hB hBm
    (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a).continuous.measurable
    (tanakaSmoothShift_error (tanakaSmoothingScale_pos n).le a) T
  let A := brownianTanakaApproxDifferenceL2 B F T hM
  change ‖A - brownianTanakaSmoothIntegral hB hBm hjoint a T n‖ ≤ _
  calc
    _ ≤ ‖A‖ + ‖brownianTanakaSmoothIntegral hB hBm hjoint a T n‖ := norm_sub_le _ _
    _ ≤ Real.sqrt T.val + Real.sqrt T.val :=
      add_le_add (brownianLipschitzDifferenceL2_norm_le hB hF T hM)
        (brownianTanakaSmoothIntegral_norm_le hB hBm hjoint a T n)
    _ = _ := by ring

end TimeTraps.Probability
