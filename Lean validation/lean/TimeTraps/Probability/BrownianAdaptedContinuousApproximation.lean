module

public import TimeTraps.Probability.BrownianAdaptedContinuousProcess
public import TimeTraps.Probability.BrownianBoundedIntegrandLimit

@[expose] public section

/-! Product-L² convergence for bounded continuous-path processes. The
dominating function is the finite time cutoff times the squared uniform
bound. No Brownian law, predictable density, or rate of continuity is
needed for this analytic convergence statement. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {H : ℝ≥0 → Ω → ℝ} {M : ℝ≥0}

theorem brownianAdaptedContinuous_step_error_bound
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    (brownianSquareStepProcess H T n p - brownianSquareProcess H T p) ^ 2 ≤
      (2 * M.val) ^ 2 * brownianIntervalIndicator 0 T p.1 := by
  have hA := brownianAdaptedContinuous_step_bound hb T n p
  have hS := brownianAdaptedContinuous_cutoff_bound hb T p
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · have hi : brownianIntervalIndicator 0 T p.1 = 1 := Set.indicator_of_mem hp _
    rw [hi, mul_one] at hA hS ⊢
    have he : |brownianSquareStepProcess H T n p - brownianSquareProcess H T p| ≤ 2 * M.val :=
      (abs_sub _ _).trans (by linarith)
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) M.property)).mpr he
  · have hi : brownianIntervalIndicator 0 T p.1 = 0 := Set.indicator_of_notMem hp _
    rw [hi, mul_zero] at hA hS ⊢
    have ha : brownianSquareStepProcess H T n p = 0 := abs_eq_zero.mp (le_antisymm hA (abs_nonneg _))
    have hs : brownianSquareProcess H T p = 0 := abs_eq_zero.mp (le_antisymm hS (abs_nonneg _))
    simp only [ha, hs, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl]

theorem brownianAdaptedContinuous_squared_error_tendsto [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0) :
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
  have hlim : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => (brownianSquareStepProcess H T n p - brownianSquareProcess H T p) ^ 2)
        atTop (𝓝 0) := by
    filter_upwards [brownianAdaptedContinuous_step_tendsto_ae hcont T] with p hp
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hp.sub_const (brownianSquareProcess H T p)).pow 2
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => (2 * M.val) ^ 2 * brownianIntervalIndicator 0 T p.1)
    (fun n => (((brownianAdaptedContinuous_step_measurable hH T n).sub
      (brownianSquareProcess_measurable hjoint T)).pow_const 2).aestronglyMeasurable) hbInt
    (fun n => Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_sq, Pi.sub_apply] using
        brownianAdaptedContinuous_step_error_bound hb T n p)) hlim
  simpa only [Pi.sub_apply, integral_zero] using hd

theorem brownianAdaptedContinuous_L2_tendsto [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0)
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
    simpa only [he] using brownianAdaptedContinuous_squared_error_tendsto hjoint hb hcont T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
