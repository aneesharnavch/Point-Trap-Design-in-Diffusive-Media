module

public import TimeTraps.Probability.BrownianIntegralSquareFinite
public import TimeTraps.Probability.BrownianJointMeasurability

@[expose] public section

/-! The actual time-times-sample process 1_(0,T](s) B_s belongs to L2.
Its integrability follows from Brownian second moments and Fubini. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_eval_second_moment (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    (∫ ω, B t ω ^ 2 ∂P) = t.val := by
  calc
    _ = ∫ ω, (B t ω - B 0 ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      rw [hω, sub_zero]
    _ = |t.val - (0 : ℝ≥0).val| := brownian_increment_second_moment hB 0 t
    _ = t.val := (congrArg abs (sub_zero t.val)).trans (abs_of_nonneg t.coe_nonneg)

noncomputable def brownianSquareProcess (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (p : ℝ × Ω) : ℝ :=
  (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * B p.1.toNNReal p.2

theorem brownianSquareProcess_measurable
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (brownianSquareProcess B T) :=
  ((measurable_const.indicator measurableSet_Ioc).comp measurable_fst).mul
    (hjoint.comp ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd))

theorem brownianSquareProcess_sample_square (hB : IsPreBrownianReal B P) (T : ℝ≥0) (r : ℝ) :
    (∫ ω, brownianSquareProcess B T (r, ω) ^ 2 ∂P) =
      (Ioc (0 : ℝ) T.val).indicator (fun r => r) r := by
  by_cases hr : r ∈ Ioc (0 : ℝ) T.val
  · simp only [brownianSquareProcess,
      Set.indicator_of_mem hr, one_mul]
    rw [brownian_eval_second_moment hB, Real.toNNReal_of_nonneg hr.1.le]
    rfl
  · simp only [brownianSquareProcess,
      Set.indicator_of_notMem hr, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero]

theorem brownianSquareProcess_memLp (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MemLp (brownianSquareProcess B T) 2 (volume.prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply (memLp_two_iff_integrable_sq (brownianSquareProcess_measurable hjoint T).aestronglyMeasurable).mpr
  apply (integrable_prod_iff ((brownianSquareProcess_measurable hjoint T).pow_const 2).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with r
    by_cases hr : r ∈ Ioc (0 : ℝ) T.val
    · simpa only [brownianSquareProcess,
        Set.indicator_of_mem hr, one_mul] using brownian_eval_integrable_sq hB r.toNNReal
    · simp only [brownianSquareProcess,
        Set.indicator_of_notMem hr, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact integrable_zero _ _ _
  · have he : (fun r => ∫ ω, ‖brownianSquareProcess B T (r, ω) ^ 2‖ ∂P) =
        (Ioc (0 : ℝ) T.val).indicator (fun r => r) := by
      funext r
      simp only [Real.norm_eq_abs, abs_sq]
      exact brownianSquareProcess_sample_square hB T r
    rw [he]
    exact (continuous_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

noncomputable def brownianSquareProcessL2 (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
  (brownianSquareProcess_memLp hB hjoint T).toLp (brownianSquareProcess B T)

theorem brownianSquareProcessL2_coe (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianSquareProcessL2 hB hjoint T =ᵐ[volume.prod P] brownianSquareProcess B T :=
  (brownianSquareProcess_memLp hB hjoint T).coeFn_toLp

end TimeTraps.Probability
