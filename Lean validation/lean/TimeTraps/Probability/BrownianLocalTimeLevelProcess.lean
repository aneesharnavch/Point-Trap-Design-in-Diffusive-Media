module

public import TimeTraps.Probability.BrownianLocalTimeLevelNull
public import TimeTraps.Probability.BrownianSignIntegrandLimitProcess

@[expose] public section

/-! Varying the level gives convergence of actual sign processes in the
finite product-L² norm. The sign discontinuity is excluded by the proved
positive-time Gaussian law, and the squared errors are dominated by
four times the finite-window indicator. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSign_level_tendsto {u : ℕ → ℝ} {a x : ℝ}
    (hu : Tendsto u atTop (𝓝 a)) (hx : x ≠ a) :
    Tendsto (fun n => Real.sign (x - u n)) atTop (𝓝 (Real.sign (x - a))) := by
  apply tendsto_const_nhds.congr'
  rcases lt_or_gt_of_ne hx with hxa | hax
  · filter_upwards [hu.eventually (Ioi_mem_nhds hxa)] with n hn
    rw [Real.sign_of_neg (sub_neg.mpr hxa), Real.sign_of_neg (sub_neg.mpr hn)]
  · filter_upwards [hu.eventually (Iio_mem_nhds hax)] with n hn
    rw [Real.sign_of_pos (sub_pos.mpr hax), Real.sign_of_pos (sub_pos.mpr hn)]

theorem brownianSignProcess_level_error_bound (B : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (T : ℝ≥0) (p : ℝ × Ω) :
    (brownianSignProcess B b T p - brownianSignProcess B a T p) ^ 2 ≤
      4 * brownianIntervalIndicator 0 T p.1 :=
  brownianSignProcess_bounded_error B (g := fun x => Real.sign (x - b))
    (fun x => brownianSign_abs_le (x - b)) a T p

theorem brownianSignProcess_level_tendsto_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (𝓝 a)) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => brownianSignProcess B (u n) T p) atTop (𝓝 (brownianSignProcess B a T p)) := by
  filter_upwards [brownian_positive_time_ne_level_prod_ae hB hjoint a T] with p hp
  by_cases ht : p.1 ∈ Ioc (0 : ℝ) T.val
  · exact (brownianSign_level_tendsto hu (hp ht)).const_mul
      ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1)
  · have hz (b : ℝ) : brownianSignProcess B b T p = 0 := by
      change (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * _ = 0
      rw [indicator_of_notMem ht, zero_mul]
    simp only [hz]
    exact tendsto_const_nhds

theorem brownianSignProcess_level_squared_error_tendsto (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {u : ℕ → ℝ} {a : ℝ} (hu : Tendsto u atTop (𝓝 a)) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p, (brownianSignProcess B (u n) T p - brownianSignProcess B a T p) ^ 2
      ∂(volume : Measure ℝ).prod P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hb : Integrable (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1) (volume.prod P) := by
    have hi := (brownianIntervalIndicator_integrable 0 T).mul_prod
      (integrable_const (4 : ℝ) : Integrable (fun _ : Ω => (4 : ℝ)) P)
    apply hi.congr
    filter_upwards [] with p
    exact mul_comm _ _
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1)
    (fun n => (((brownianSignProcess_measurable hjoint (u n) T).sub
      (brownianSignProcess_measurable hjoint a T)).pow_const 2).aestronglyMeasurable) hb
    (fun n => Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_sq, Pi.sub_apply] using
        brownianSignProcess_level_error_bound B a (u n) T p))
    (by
      filter_upwards [brownianSignProcess_level_tendsto_ae hB hjoint hu T] with p hp
      simpa only [Pi.sub_apply, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        (hp.sub_const (brownianSignProcess B a T p)).pow 2)
  simpa only [Pi.sub_apply, integral_zero] using hd

end TimeTraps.Probability
