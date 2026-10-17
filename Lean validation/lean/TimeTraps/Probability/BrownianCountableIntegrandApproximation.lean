module

public import TimeTraps.Probability.BrownianCountableIntegrandProcess
public import TimeTraps.Probability.BrownianAdaptedContinuousApproximation

@[expose] public section

/-! Product-L² convergence of uniformly bounded dyadic samples follows
from product-almost-everywhere convergence. This version needs no global
continuity of the sampled paths, so it applies to a bounded Borel function
of Brownian motion with countably many possible discontinuities. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {H : ℝ≥0 → Ω → ℝ} {M : ℝ≥0}

theorem brownianBoundedStep_squared_error_tendsto [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0)
    (hlim : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => brownianSquareStepProcess H T n p) atTop
        (𝓝 (brownianSquareProcess H T p))) :
    Tendsto (fun n => ∫ p,
      (brownianSquareStepProcess H T n p - brownianSquareProcess H T p) ^ 2
        ∂(volume : Measure ℝ).prod P) atTop (𝓝 0) := by
  have hH (t : ℝ≥0) : Measurable (H t) :=
    hjoint.comp (measurable_const.prodMk measurable_id)
  have hbInt : Integrable (fun p : ℝ × Ω => (2 * M.val) ^ 2 * brownianIntervalIndicator 0 T p.1)
      (volume.prod P) := by
    have hi := (brownianIntervalIndicator_integrable 0 T).mul_prod
      (integrable_const ((2 * M.val) ^ 2) : Integrable (fun _ : Ω => (2 * M.val) ^ 2) P)
    apply hi.congr
    filter_upwards [] with p
    exact mul_comm _ _
  have he : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => (brownianSquareStepProcess H T n p - brownianSquareProcess H T p) ^ 2)
        atTop (𝓝 0) := by
    filter_upwards [hlim] with p hp
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hp.sub_const (brownianSquareProcess H T p)).pow 2
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => (2 * M.val) ^ 2 * brownianIntervalIndicator 0 T p.1)
    (fun n => (((brownianAdaptedContinuous_step_measurable hH T n).sub
      (brownianSquareProcess_measurable hjoint T)).pow_const 2).aestronglyMeasurable) hbInt
    (fun n => Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_sq, Pi.sub_apply] using
        brownianAdaptedContinuous_step_error_bound hb T n p)) he
  simpa only [Pi.sub_apply, integral_zero] using hd

theorem brownianBoundedStep_L2_tendsto [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0)
    (hlim : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => brownianSquareStepProcess H T n p) atTop
        (𝓝 (brownianSquareProcess H T p)))
    (A : ℕ → Lp ℝ 2 ((volume : Measure ℝ).prod P)) (S : Lp ℝ 2 ((volume : Measure ℝ).prod P))
    (hA : ∀ n, A n =ᵐ[volume.prod P] brownianSquareStepProcess H T n)
    (hS : S =ᵐ[volume.prod P] brownianSquareProcess H T) :
    Tendsto A atTop (𝓝 S) := by
  have he (n : ℕ) : ‖A n - S‖ ^ 2 = ∫ p,
      (brownianSquareStepProcess H T n p - brownianSquareProcess H T p) ^ 2
        ∂(volume : Measure ℝ).prod P := by
    calc
      _ = ∫ p, (A n - S) p ^ 2 ∂(volume : Measure ℝ).prod P := by
        simpa only [Lp.toLp_coeFn] using memLp_norm_toLp_sq (Lp.memLp (A n - S))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (A n) S, hA n, hS] with p hd ha hs
        rw [hd, Pi.sub_apply, ha, hs]
  have hs : Tendsto (fun n => ‖A n - S‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using brownianBoundedStep_squared_error_tendsto hjoint hb T hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
