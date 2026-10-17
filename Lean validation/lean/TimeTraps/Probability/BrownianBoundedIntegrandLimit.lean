module

public import TimeTraps.Probability.BrownianBoundedIntegrandProcess
public import TimeTraps.Probability.BrownianSignIntegrandStochastic

@[expose] public section

/-! Bounded pointwise convergence gives product-L² convergence. If the
approximating processes belong to the independently closed Ito-integrand
space, the limit belongs to it and the actual stochastic integrals converge.
No density assertion for all adapted or predictable processes is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℕ → ℝ → ℝ} {h : ℝ → ℝ} {M : ℝ}

theorem brownianBoundedProcess_squared_error_tendsto [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : ∀ n, Measurable (g n)) (hh : Measurable h)
    (hb : ∀ n x, |g n x| ≤ M) (hhb : ∀ x, |h x| ≤ M)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (h x))) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p,
      (brownianBoundedProcess B (g n) T p - brownianBoundedProcess B h T p) ^ 2
        ∂(volume : Measure ℝ).prod P) atTop (𝓝 0) := by
  have hbInt : Integrable (fun p : ℝ × Ω => (2 * M) ^ 2 * brownianIntervalIndicator 0 T p.1)
      (volume.prod P) := by
    have hi := (brownianIntervalIndicator_integrable 0 T).mul_prod
      (integrable_const ((2 * M) ^ 2) : Integrable (fun _ : Ω => (2 * M) ^ 2) P)
    apply hi.congr
    filter_upwards [] with p
    exact mul_comm _ _
  have hd := tendsto_integral_of_dominated_convergence
    (fun p : ℝ × Ω => (2 * M) ^ 2 * brownianIntervalIndicator 0 T p.1)
    (fun n => (((brownianBoundedProcess_measurable (hg n) hjoint T).sub
      (brownianBoundedProcess_measurable hh hjoint T)).pow_const 2).aestronglyMeasurable) hbInt
    (fun n => Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, abs_sq, Pi.sub_apply] using
        brownianBoundedProcess_error_le B (hb n) hhb T p))
    (Eventually.of_forall (fun p => by
      simpa only [Pi.sub_apply, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((brownianBoundedProcess_tendsto B hlim T p).sub_const
          (brownianBoundedProcess B h T p)).pow 2))
  simpa only [Pi.sub_apply, integral_zero] using hd

theorem brownianBoundedProcessL2_tendsto [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : ∀ n, Measurable (g n)) (hh : Measurable h)
    (hb : ∀ n x, |g n x| ≤ M) (hhb : ∀ x, |h x| ≤ M)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (h x))) (T : ℝ≥0)
    (A : ℕ → Lp ℝ 2 ((volume : Measure ℝ).prod P)) (S : Lp ℝ 2 ((volume : Measure ℝ).prod P))
    (hA : ∀ n, A n =ᵐ[volume.prod P] brownianBoundedProcess B (g n) T)
    (hS : S =ᵐ[volume.prod P] brownianBoundedProcess B h T) :
    Tendsto A atTop (𝓝 S) := by
  have he (n : ℕ) : ‖A n - S‖ ^ 2 = ∫ p,
      (brownianBoundedProcess B (g n) T p - brownianBoundedProcess B h T p) ^ 2
        ∂(volume : Measure ℝ).prod P := by
    calc
      _ = ∫ p, (A n - S) p ^ 2 ∂(volume : Measure ℝ).prod P := by
        simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp (A n - S))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (A n) S, hA n, hS] with p hd ha hs
        rw [hd, Pi.sub_apply, ha, hs]
  have hs : Tendsto (fun n => ‖A n - S‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using brownianBoundedProcess_squared_error_tendsto hjoint hg hh hb hhb hlim T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

theorem brownianBoundedIntegrand_limit (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : ∀ n, Measurable (g n)) (hb : ∀ n x, |g n x| ≤ M)
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (h x))) (T : ℝ≥0)
    (U : ℕ → brownianIntegralSpace B hBm P)
    (hU : ∀ n, (U n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianBoundedProcess B (g n) T) :
    ∃ u : brownianIntegralSpace B hBm P,
      ((u : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] brownianBoundedProcess B h T) ∧
      Tendsto U atTop (𝓝 u) ∧
      Tendsto (fun n => brownianIntegral hB (U n)) atTop (𝓝 (brownianIntegral hB u)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hh : Measurable h := measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.mpr hlim)
  have hhb : ∀ x, |h x| ≤ M := fun x =>
    le_of_tendsto (hlim x).abs (Eventually.of_forall (fun n => hb n x))
  let hmem := brownianBoundedProcess_memLp (P := P) hh hhb hjoint T
  let S := brownianBoundedProcessL2 B h T hmem
  have hS : S =ᵐ[volume.prod P] brownianBoundedProcess B h T :=
    brownianBoundedProcessL2_coe B h T hmem
  have hconv := brownianBoundedProcessL2_tendsto hjoint hg hh hb hhb hlim T
    (fun n => (U n : Lp ℝ 2 ((volume : Measure ℝ).prod P))) S hU hS
  have hc : IsClosed (brownianIntegralSpace B hBm P : Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (brownianIntegralStepSpace B hBm P).isClosed_topologicalClosure
  have hSmem : S ∈ brownianIntegralSpace B hBm P :=
    hc.mem_of_tendsto hconv (Eventually.of_forall (fun n => (U n).property))
  let u : brownianIntegralSpace B hBm P := ⟨S, hSmem⟩
  have hu : Tendsto U atTop (𝓝 u) := tendsto_subtype_rng.mpr hconv
  exact ⟨u, hS, hu, (brownianIntegral hB).continuous.continuousAt.tendsto.comp hu⟩

end TimeTraps.Probability
