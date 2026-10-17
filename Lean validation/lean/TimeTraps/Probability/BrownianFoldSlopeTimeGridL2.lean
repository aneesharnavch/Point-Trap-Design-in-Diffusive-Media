module

public import TimeTraps.Probability.BrownianFoldSlopeTimeGrid
public import TimeTraps.Probability.BrownianFoldSlopeIntegrand

@[expose] public section

/-! The actual left-time-grid fold slopes converge in product L² to
the already constructed closed-domain fold-slope integrand. The proof
uses the bounded square error and product-almost-everywhere convergence,
without identifying the transformed noise as Brownian. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianFoldSlopeTimeGrid_error_le (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    (brownianFoldSlopeTimeGrid B L x σ T n p -
      brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2 ≤
        4 * brownianIntervalIndicator 0 T p.1 := by
  have hA := brownianFoldSlopeTimeGrid_abs_le B L hL x σ T n p
  have hS := brownianBoundedProcess_abs_le B (fun z => reflectedFoldSlope_bound L hL (x + σ * z)) T p
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · have hi : brownianIntervalIndicator 0 T p.1 = 1 := Set.indicator_of_mem hp _
    rw [hi] at hA hS ⊢
    have he : |brownianFoldSlopeTimeGrid B L x σ T n p -
        brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p| ≤ 2 :=
      (abs_sub _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr he
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num, mul_one] using hs
  · have hi : brownianIntervalIndicator 0 T p.1 = 0 := Set.indicator_of_notMem hp _
    rw [hi] at hA hS ⊢
    have ha : brownianFoldSlopeTimeGrid B L x σ T n p = 0 := abs_eq_zero.mp (le_antisymm hA (abs_nonneg _))
    have hs : brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p = 0 :=
      abs_eq_zero.mp (le_antisymm (by simpa only [mul_zero] using hS) (abs_nonneg _))
    simp only [ha, hs, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]

theorem brownianFoldSlopeTimeGrid_squared_error_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p, (brownianFoldSlopeTimeGrid B L x σ T n p -
      brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2
        ∂(volume : Measure ℝ).prod P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hB.toIsPreBrownianReal.hasLaw_eval 0).isProbabilityMeasure
  have hh : Measurable (fun z => reflectedFoldSlope L (x + σ * z)) :=
    (reflectedFoldSlope_measurable L hL).comp (measurable_const.add (measurable_const.mul measurable_id))
  have hbInt : Integrable (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1) (volume.prod P) := by
    have hi := (brownianIntervalIndicator_integrable 0 T).mul_prod
      (integrable_const (4 : ℝ) : Integrable (fun _ : Ω => (4 : ℝ)) P)
    apply hi.congr
    filter_upwards [] with p
    exact mul_comm _ _
  have hlim : ∀ᵐ p ∂(volume : Measure ℝ).prod P,
      Tendsto (fun n => (brownianFoldSlopeTimeGrid B L x σ T n p -
        brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2) atTop (𝓝 0) := by
    filter_upwards [brownianFoldSlopeTimeGrid_tendsto_ae hB hjoint L hL x hσ T] with p hp
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hp.sub_const (brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p)).pow 2
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => 4 * brownianIntervalIndicator 0 T p.1)
    (fun n => (((brownianFoldSlopeTimeGrid_measurable hBm L hL x σ T n).sub
      (brownianBoundedProcess_measurable hh hjoint T)).pow_const 2).aestronglyMeasurable) hbInt
    (fun n => Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_sq, Pi.sub_apply] using
        brownianFoldSlopeTimeGrid_error_le B L hL x σ T n p)) hlim
  simpa only [Pi.sub_apply, integral_zero] using hd

def brownianFoldSlopeTimeGridL2 (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) : Lp ℝ 2 ((volume : Measure ℝ).prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownianFoldSlopeTimeGrid_memLp hBm L hL x σ T n).toLp (brownianFoldSlopeTimeGrid B L x σ T n)

theorem brownianFoldSlopeTimeGridL2_coe (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) :
    brownianFoldSlopeTimeGridL2 hB hBm L hL x σ T n =ᵐ[volume.prod P] brownianFoldSlopeTimeGrid B L x σ T n := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact MemLp.coeFn_toLp (brownianFoldSlopeTimeGrid_memLp hBm L hL x σ T n)

theorem brownianFoldSlopeTimeGridL2_tendsto (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    Tendsto (fun n => brownianFoldSlopeTimeGridL2 hB.toIsPreBrownianReal hBm L hL x σ T n) atTop
      (𝓝 (brownianFoldSlopeIntegrand hB.toIsPreBrownianReal hBm hjoint L hL x hσ T :
        Lp ℝ 2 ((volume : Measure ℝ).prod P))) := by
  let A (n : ℕ) := brownianFoldSlopeTimeGridL2 hB.toIsPreBrownianReal hBm L hL x σ T n
  let S : Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
    brownianFoldSlopeIntegrand hB.toIsPreBrownianReal hBm hjoint L hL x hσ T
  have he (n : ℕ) : ‖A n - S‖ ^ 2 = ∫ p, (brownianFoldSlopeTimeGrid B L x σ T n p -
      brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + σ * z)) T p) ^ 2 ∂volume.prod P := by
    calc
      _ = ∫ p, (A n - S) p ^ 2 ∂volume.prod P := by
        simpa only [Lp.toLp_coeFn] using memLp_norm_toLp_sq (Lp.memLp (A n - S))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (A n) S,
          brownianFoldSlopeTimeGridL2_coe hB.toIsPreBrownianReal hBm L hL x σ T n,
          brownianFoldSlopeIntegrand_coe hB.toIsPreBrownianReal hBm hjoint L hL x hσ T] with p hd ha hs
        rw [hd, Pi.sub_apply, ha, hs]
  have hs : Tendsto (fun n => ‖A n - S‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using brownianFoldSlopeTimeGrid_squared_error_tendsto hB hBm hjoint L hL x hσ T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability

end
