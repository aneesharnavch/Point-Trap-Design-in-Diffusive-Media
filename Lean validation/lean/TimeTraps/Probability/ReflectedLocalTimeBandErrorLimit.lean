module

public import TimeTraps.Probability.ReflectedLocalTimeBandErrorAverage

@[expose] public section

/-! The genuine spatial averages of the maximal error tend to zero in
mean square. The limit is derived from continuity of the L2-valued
family and its zero value at the central level. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedBandErrorAverageL2_interval (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ} (hh : 0 ≤ h) :
    reflectedBandErrorAverageL2 L hL x hσ T a h =
      (1 / (2 * h)) • ∫ b in (a.val - h)..(a.val + h), reflectedBandErrorL2 L hL x hσ T a b := by
  rw [intervalIntegral.integral_of_le (by linarith : a.val - h ≤ a.val + h), integral_Ioc_eq_integral_Ioo]
  rfl

theorem reflectedBandErrorAverageL2_tendsto (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    Tendsto (reflectedBandErrorAverageL2 L hL x hσ T a) (𝓝[>] 0) (𝓝 0) := by
  have ht := continuous_band_average_tendsto (reflectedBandErrorL2_continuous L hL x hσ T a) a.val
  rw [reflectedBandErrorL2_center] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (reflectedBandErrorAverageL2_interval L hL x hσ T a (show 0 ≤ h from (show 0 < h from hh).le)).symm

theorem reflectedBandErrorAverage_toLp (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (h : ℝ) :
    (reflectedBandErrorAverage_memLp L hL x hσ T a h).toLp (reflectedBandErrorAverage L hL x hσ T a h) =
      reflectedBandErrorAverageL2 L hL x hσ T a h := by
  apply Lp.ext
  exact (reflectedBandErrorAverage_memLp L hL x hσ T a h).coeFn_toLp.trans
    (reflectedBandErrorAverageL2_coe L hL x hσ T a h).symm

theorem reflectedBandErrorAverage_square_tendsto (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    Tendsto (fun h => ∫ ω, reflectedBandErrorAverage L hL x hσ T a h ω ^ 2 ∂brownianDyadicMeasure)
      (𝓝[>] 0) (𝓝 0) := by
  have he (h : ℝ) : (∫ ω, reflectedBandErrorAverage L hL x hσ T a h ω ^ 2 ∂brownianDyadicMeasure) =
      ‖reflectedBandErrorAverageL2 L hL x hσ T a h‖ ^ 2 := by
    rw [← memLp_norm_toLp_sq (reflectedBandErrorAverage_memLp L hL x hσ T a h),
      reflectedBandErrorAverage_toLp]
  simpa only [he, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (reflectedBandErrorAverageL2_tendsto L hL x hσ T a).norm.pow 2

theorem reflectedBandErrorAverage_nonneg (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) {h : ℝ} (hh : 0 < h) (ω : ℕ → ℝ) :
    0 ≤ reflectedBandErrorAverage L hL x hσ T a h ω :=
  mul_nonneg (by positivity) (integral_nonneg (fun b => reflectedBandErrorVersion_nonneg L hL x hσ T a b ω))

end TimeTraps.Probability
