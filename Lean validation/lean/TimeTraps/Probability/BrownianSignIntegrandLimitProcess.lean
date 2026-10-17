module

public import TimeTraps.Probability.BrownianSignIntegrandStochastic

@[expose] public section

/-! Any uniformly bounded Lipschitz approximation converging pointwise
to sign(x-a) has the same actual product-L² limit. Lipschitz constants
may vary without a uniform bound. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSignProcess_bounded_error (B : ℝ≥0 → Ω → ℝ)
    {g : ℝ → ℝ} (hb : ∀ x, |g x| ≤ 1) (a : ℝ) (T : ℝ≥0) (p : ℝ × Ω) :
    (brownianLipschitzProcess B g T p - brownianSignProcess B a T p) ^ 2 ≤
      4 * brownianIntervalIndicator 0 T p.1 := by
  change ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * g (B p.1.toNNReal p.2) -
    (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * Real.sign (B p.1.toNNReal p.2 - a)) ^ 2 ≤
      4 * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · simp only [Set.indicator_of_mem hp, one_mul, mul_one]
    have hg := abs_le.mp (hb (B p.1.toNNReal p.2))
    have hs := abs_le.mp (brownianSign_abs_le (B p.1.toNNReal p.2 - a))
    nlinarith [hg.1, hg.2, hs.1, hs.2]
  · simp only [Set.indicator_of_notMem hp, zero_mul, mul_zero, sub_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl]

variable {g : ℕ → ℝ → ℝ} {K : ℕ → ℝ≥0} {a : ℝ}

theorem brownianSignProcess_general_tendsto (B : ℝ≥0 → Ω → ℝ)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (Real.sign (x - a)))) (T : ℝ≥0) (p : ℝ × Ω) :
    Tendsto (fun n => brownianLipschitzProcess B (g n) T p) atTop (𝓝 (brownianSignProcess B a T p)) :=
  (hlim (B p.1.toNNReal p.2)).const_mul ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1)

theorem brownianSignProcess_general_squared_error_tendsto (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : ∀ n, LipschitzWith (K n) (g n)) (hb : ∀ n x, |g n x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (Real.sign (x - a)))) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p, (brownianLipschitzProcess B (g n) T p - brownianSignProcess B a T p) ^ 2
      ∂(volume : Measure ℝ).prod P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hbInt : Integrable (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1) (volume.prod P) := by
    have hi := (brownianIntervalIndicator_integrable 0 T).mul_prod
      (integrable_const (4 : ℝ) : Integrable (fun _ : Ω => (4 : ℝ)) P)
    apply hi.congr
    filter_upwards [] with p
    exact mul_comm _ _
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1)
    (fun n => (((brownianLipschitzProcess_measurable (hg n) hjoint T).sub
      (brownianSignProcess_measurable hjoint a T)).pow_const 2).aestronglyMeasurable) hbInt
    (fun n => Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_sq, Pi.sub_apply] using brownianSignProcess_bounded_error B (hb n) a T p))
    (Eventually.of_forall (fun p => by
      simpa only [Pi.sub_apply, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((brownianSignProcess_general_tendsto B hlim T p).sub_const (brownianSignProcess B a T p)).pow 2))
  simpa only [Pi.sub_apply, integral_zero] using hd

theorem brownianSignProcessL2_general_tendsto (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : ∀ n, LipschitzWith (K n) (g n)) (hb : ∀ n x, |g n x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (Real.sign (x - a)))) (T : ℝ≥0) :
    Tendsto (fun n => brownianLipschitzProcessL2 hB (hg n) hjoint T) atTop
      (𝓝 (brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T))) := by
  let A (n : ℕ) := brownianLipschitzProcessL2 hB (hg n) hjoint T
  let S := brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T)
  have he (n : ℕ) : ‖A n - S‖ ^ 2 = ∫ p,
      (brownianLipschitzProcess B (g n) T p - brownianSignProcess B a T p) ^ 2
        ∂(volume : Measure ℝ).prod P := by
    calc
      _ = ∫ p, (A n - S) p ^ 2 ∂(volume : Measure ℝ).prod P := by
        simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp (A n - S))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (A n) S, brownianLipschitzProcessL2_coe hB (hg n) hjoint T,
          brownianSignProcessL2_coe B a T (brownianSignProcess_memLp hB hjoint a T)] with p hd ha hs
        rw [hd, Pi.sub_apply, ha, hs]
  have hs : Tendsto (fun n => ‖A n - S‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using brownianSignProcess_general_squared_error_tendsto hB hjoint hg hb hlim T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
