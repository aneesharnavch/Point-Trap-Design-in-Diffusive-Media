module

public import TimeTraps.Probability.BrownianSignIntegrandProcess
public import TimeTraps.Analysis.IntegralCauchySchwarz

@[expose] public section

/-! Dominated convergence on the finite time window identifies the
actual sign process as the product-L² limit of Lipschitz processes. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSignProcess_approximation_tendsto (B : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (T : ℝ≥0) (p : ℝ × Ω) :
    Tendsto (fun n => brownianLipschitzProcess B (brownianSignApprox a n) T p) atTop
      (𝓝 (brownianSignProcess B a T p)) :=
  (brownianSignApprox_tendsto a (B p.1.toNNReal p.2)).const_mul
    ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1)

theorem brownianSignProcess_squared_error_tendsto (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p, (brownianLipschitzProcess B (brownianSignApprox a n) T p -
      brownianSignProcess B a T p) ^ 2 ∂(volume : Measure ℝ).prod P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hb : Integrable (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1) (volume.prod P) := by
    have hi := (brownianIntervalIndicator_integrable 0 T).mul_prod
      (integrable_const (4 : ℝ) : Integrable (fun _ : Ω => (4 : ℝ)) P)
    apply hi.congr
    filter_upwards [] with p
    exact mul_comm _ _
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1)
    (fun n => (((brownianLipschitzProcess_measurable (brownianSignApprox_lipschitz a n) hjoint T).sub
      (brownianSignProcess_measurable hjoint a T)).pow_const 2).aestronglyMeasurable) hb
    (fun n => Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_sq, Pi.sub_apply] using brownianSignProcess_approximation_bound B a T n p))
    (Eventually.of_forall (fun p => by
      simpa only [Pi.sub_apply, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((brownianSignProcess_approximation_tendsto B a T p).sub_const (brownianSignProcess B a T p)).pow 2))
  simpa only [Pi.sub_apply, integral_zero] using hd

theorem brownianSignProcessL2_tendsto (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => brownianLipschitzProcessL2 hB (brownianSignApprox_lipschitz a n) hjoint T) atTop
      (𝓝 (brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T))) := by
  let A (n : ℕ) := brownianLipschitzProcessL2 hB (brownianSignApprox_lipschitz a n) hjoint T
  let S := brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T)
  have he (n : ℕ) : ‖A n - S‖ ^ 2 = ∫ p,
      (brownianLipschitzProcess B (brownianSignApprox a n) T p - brownianSignProcess B a T p) ^ 2
        ∂(volume : Measure ℝ).prod P := by
    calc
      _ = ∫ p, (A n - S) p ^ 2 ∂(volume : Measure ℝ).prod P := by
        simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp (A n - S))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (A n) S,
          brownianLipschitzProcessL2_coe hB (brownianSignApprox_lipschitz a n) hjoint T,
          brownianSignProcessL2_coe B a T (brownianSignProcess_memLp hB hjoint a T)] with p hd ha hs
        rw [hd, Pi.sub_apply, ha, hs]
  have hs : Tendsto (fun n => ‖A n - S‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using brownianSignProcess_squared_error_tendsto hB hjoint a T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
