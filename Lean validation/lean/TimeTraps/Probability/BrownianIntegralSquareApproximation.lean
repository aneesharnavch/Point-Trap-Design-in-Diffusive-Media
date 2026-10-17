module

public import TimeTraps.Probability.BrownianIntegralSquareGrid
public import TimeTraps.Probability.BrownianIntegralSquareProcess

@[expose] public section

/-! Left-grid approximation of the actual Brownian integrand in product
L2, derived from the increment second moment on each dyadic cell. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSquareStep_sample_error_le (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (n : ℕ) (r : ℝ) :
    (∫ ω, (brownianSquareProcess B T (r, ω) - brownianSquareStepProcess B T n (r, ω)) ^ 2 ∂P) ≤
      (Ioc (0 : ℝ) T.val).indicator (fun _ => T.val / (2 : ℝ) ^ n) r := by
  by_cases hr : r ∈ Ioc (0 : ℝ) T.val
  · obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hr
    have he : (fun ω => (brownianSquareProcess B T (r, ω) - brownianSquareStepProcess B T n (r, ω)) ^ 2) =
        fun ω => (B r.toNNReal ω - B (brownianDyadicGrid T n i.castSucc) ω) ^ 2 := by
      funext ω
      rw [brownianSquareStepProcess_cell B T n ω i hi]
      simp only [brownianSquareProcess, Set.indicator_of_mem hr, one_mul]
    rw [he, Set.indicator_of_mem hr, brownian_increment_second_moment hB]
    have hrr : r.toNNReal.val = r := by rw [Real.toNNReal_of_nonneg hr.1.le]; rfl
    rw [hrr, abs_of_nonneg (sub_nonneg.mpr hi.1.le)]
    have hg := brownianDyadicGrid_gap T n i
    rw [abs_of_nonneg (sub_nonneg.mpr (hi.1.le.trans hi.2))] at hg
    exact (sub_le_sub_right hi.2 _).trans_eq hg
  · have he : (fun ω => (brownianSquareProcess B T (r, ω) - brownianSquareStepProcess B T n (r, ω)) ^ 2) =
        fun _ : Ω => (0 : ℝ) := by
      funext ω
      rw [brownianSquareStepProcess_outside B T n ω hr]
      simp only [brownianSquareProcess, Set.indicator_of_notMem hr, zero_mul, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [he, integral_zero, Set.indicator_of_notMem hr]

theorem brownianSquareStep_process_error_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (n : ℕ) :
    ‖(brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
      brownianSquareProcessL2 hB hjoint T‖ ^ 2 ≤ T.val ^ 2 / (2 : ℝ) ^ n := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hs : MemLp (brownianSquareStepProcess B T n) 2 (volume.prod P) :=
    (Lp.memLp (brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P))).ae_eq
      (brownianSquareStepIntegrand_coe hB hBm T n)
  have hd := ((brownianSquareProcess_memLp hB hjoint T).sub hs).integrable_sq
  change Integrable (fun p => (brownianSquareProcess B T p - brownianSquareStepProcess B T n p) ^ 2)
    (volume.prod P) at hd
  have he : ‖(brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
      brownianSquareProcessL2 hB hjoint T‖ ^ 2 =
      ∫ p, (brownianSquareProcess B T p - brownianSquareStepProcess B T n p) ^ 2 ∂volume.prod P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
      (brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      (brownianSquareProcessL2 hB hjoint T), brownianSquareStepIntegrand_coe hB hBm T n,
      brownianSquareProcessL2_coe hB hjoint T] with p hd hs ht
    rw [Real.inner_apply, hd]
    simp only [Pi.sub_apply]
    rw [hs, ht]
    ring
  rw [he, integral_prod _ hd]
  have hb : Integrable ((Ioc (0 : ℝ) T.val).indicator (fun _ => T.val / (2 : ℝ) ^ n)) volume :=
    (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) T.val) (C := T.val / (2 : ℝ) ^ n)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ioc
  calc
    _ ≤ ∫ r, (Ioc (0 : ℝ) T.val).indicator (fun _ => T.val / (2 : ℝ) ^ n) r :=
      integral_mono_ae hd.integral_prod_left hb (Filter.Eventually.of_forall (brownianSquareStep_sample_error_le hB T n))
    _ = _ := by
      have hv : (volume : Measure ℝ).real (Ioc (0 : ℝ) T.val) = T.val :=
        (Real.volume_real_Ioc_of_le T.coe_nonneg).trans (sub_zero T.val)
      have hf : (volume : Measure ℝ).real (Ioc (0 : ℝ) T.val) • (T.val / (2 : ℝ) ^ n) =
          T.val ^ 2 / (2 : ℝ) ^ n := by
        calc
          _ = T.val * (T.val / (2 : ℝ) ^ n) :=
            congrArg (fun a : ℝ => a * (T.val / (2 : ℝ) ^ n)) hv
          _ = _ := by ring
      exact (integral_indicator measurableSet_Ioc).trans ((setIntegral_const _).trans hf)

theorem brownianSquareStep_process_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Tendsto (fun n => (brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)))
      atTop (𝓝 (brownianSquareProcessL2 hB hjoint T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun n => T.val ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (T.val ^ 2)
  have hs := squeeze_zero (fun n => sq_nonneg
    ‖(brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
      brownianSquareProcessL2 hB hjoint T‖)
    (brownianSquareStep_process_error_le hB hBm hjoint T) hb
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
