module

public import TimeTraps.Probability.BrownianOccupationL1Approximation
public import TimeTraps.Probability.BrownianOccupationL1Bound
public import TimeTraps.Probability.BrownianOccupationIdentity
public import TimeTraps.Probability.BrownianItoFormulaLimit

@[expose] public section

/-! The occupation identity extends to every scalar L¹ weight.
Compactly supported continuous approximations converge on the spatial
side in actual L², while the Gaussian occupation bound controls an L¹
time-integral remainder. Almost-everywhere limit uniqueness identifies
the genuine ordinary time integral and consequently proves its L²
membership. The Brownian law is the existing zero-start law throughout. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianItoDrift_L1_difference_tendsto (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {u : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hu : ∀ n, Integrable (u n) volume)
    (hg : Integrable g volume)
    (hlim : Tendsto (fun n => ∫ x, |u n x - g x|) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |brownianItoDrift B (u n) T ω - brownianItoDrift B g T ω| ∂P)
      atTop (𝓝 0) :=
  squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => brownianItoDrift_L1_difference_bound hB hjoint T (hu n) hg)
    (by
      simpa only [mul_zero] using hlim.const_mul (2 * Real.sqrt T.val / Real.sqrt (2 * Real.pi)))

theorem brownianTanakaLevelIntegral_occupation_L1_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    brownianTanakaLevelIntegral hB hBm hjoint T g =ᵐ[P] brownianItoDrift B g T := by
  obtain ⟨u, huc, hcomp, hu, hlim⟩ := real_integrable_compact_approximation hg
  let S (n : ℕ) := brownianTanakaLevelIntegral hB hBm hjoint T (u n)
  let Y := brownianTanakaLevelIntegral hB hBm hjoint T g
  let H := brownianItoDrift B g T
  have hR (n : ℕ) : Integrable (fun ω => H ω - brownianItoDrift B (u n) T ω) P :=
    (brownianItoDrift_L1_integrable hB hjoint T hg).sub
      (brownianItoDrift_L1_integrable hB hjoint T (hu n))
  let R (n : ℕ) : Lp ℝ 1 P := (hR n).toL1 (fun ω => H ω - brownianItoDrift B (u n) T ω)
  have hRn (n : ℕ) : ‖R n‖ = ∫ ω, |brownianItoDrift B (u n) T ω - H ω| ∂P := by
    change ‖(hR n).toL1 _‖ = _
    rw [L1.norm_of_fun_eq_integral_norm]
    simp only [Real.norm_eq_abs, abs_sub_comm]
  have hRL : Tendsto R atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero, hRn]
    exact brownianItoDrift_L1_difference_tendsto hB hjoint T hu hg hlim
  have hSL : Tendsto S atTop (𝓝 Y) :=
    brownianTanakaLevelIntegral_tendsto_of_L1 hB hBm hjoint T hu hg hlim
  have he (n : ℕ) : H =ᵐ[P] (fun ω => S n ω + R n ω) := by
    filter_upwards [brownianTanakaLevelIntegral_occupation_compact_ae hB hBm hjoint
      (huc n) (hcomp n) T, (hR n).coeFn_toL1] with ω hs hr
    change H ω = brownianTanakaLevelIntegral hB hBm hjoint T (u n) ω +
      (hR n).toL1 (fun ω => H ω - brownianItoDrift B (u n) T ω) ω
    rw [hs, hr]
    ring
  exact (ae_eq_lp_limit_of_remainder S Y R H hSL hRL he).symm

theorem brownianItoDrift_L1_memLp_two (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) : MemLp (brownianItoDrift B g T) 2 P :=
  (Lp.memLp (brownianTanakaLevelIntegral hB hBm hjoint T g)).ae_eq
    (brownianTanakaLevelIntegral_occupation_L1_ae hB hBm hjoint T hg)

theorem brownianTanakaLevelIntegral_eq_occupationL1 (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    brownianTanakaLevelIntegral hB hBm hjoint T g =
      brownianItoDriftL2 B g T (brownianItoDrift_L1_memLp_two hB hBm hjoint T hg) := by
  apply Lp.ext
  exact (brownianTanakaLevelIntegral_occupation_L1_ae hB hBm hjoint T hg).trans
    (brownianItoDriftL2_coe B g T (brownianItoDrift_L1_memLp_two hB hBm hjoint T hg)).symm

end TimeTraps.Probability
