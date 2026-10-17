module

public import TimeTraps.Probability.BrownianOccupationTimeBound
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Uniformly bounded pointwise approximation of the scalar function
passes to genuine finite-time integrals, first for every path and then
in actual L2. No stochastic occupation identity is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {M : ℝ}

theorem brownianItoDrift_bounded_tendsto (hF : ∀ n, Measurable (F n))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hb : ∀ n x, |F n x| ≤ M) (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (g x)))
    (T : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => brownianItoDrift B (F n) T ω) atTop (𝓝 (brownianItoDrift B g T ω)) := by
  have hd := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) T.val))
    (F := fun n s => F n (B s.toNNReal ω)) (f := fun s => g (B s.toNNReal ω))
    (fun _ => M)
    (fun n => ((hF n).comp (hjoint.comp
      ((by fun_prop : Measurable (fun s : ℝ => s.toNNReal)).prodMk measurable_const))).aestronglyMeasurable)
    (integrable_const M)
    (fun n => Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hb n (B s.toNNReal ω))
    (Eventually.of_forall fun s => hlim (B s.toNNReal ω))
  have he (f : ℝ → ℝ) : brownianItoDrift B f T ω = ∫ s in Ioc (0 : ℝ) T.val, f (B s.toNNReal ω) :=
    intervalIntegral.integral_of_le T.coe_nonneg
  simp only [he]
  exact hd

theorem brownianItoDrift_bounded_secondMoment_tendsto [IsFiniteMeasure P]
    (hF : ∀ n, Measurable (F n)) (hg : Measurable g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hb : ∀ n x, |F n x| ≤ M) (hbg : ∀ x, |g x| ≤ M)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (g x))) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (brownianItoDrift B (F n) T ω - brownianItoDrift B g T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hM : 0 ≤ M := (abs_nonneg (g 0)).trans (hbg 0)
  have hbound (n : ℕ) (ω : Ω) :
      |brownianItoDrift B (F n) T ω - brownianItoDrift B g T ω| ≤ 2 * T.val * M := by
    calc
      _ ≤ |brownianItoDrift B (F n) T ω| + |brownianItoDrift B g T ω| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (brownianItoDrift B (F n) T ω) 0 (brownianItoDrift B g T ω)
      _ ≤ T.val * M + T.val * M := add_le_add
        (brownianItoDrift_bounded_abs (hb n) T ω) (brownianItoDrift_bounded_abs hbg T ω)
      _ = _ := by ring
  have hd := tendsto_integral_of_dominated_convergence
    (F := fun n ω => (brownianItoDrift B (F n) T ω - brownianItoDrift B g T ω) ^ 2)
    (f := fun _ : Ω => (0 : ℝ)) (fun _ : Ω => (2 * T.val * M) ^ 2)
    (fun n => (((brownianItoDrift_bounded_measurable (hF n) hjoint T).sub
      (brownianItoDrift_bounded_measurable hg hjoint T)).pow_const 2).aestronglyMeasurable)
    (integrable_const ((2 * T.val * M) ^ 2) : Integrable (fun _ : Ω => (2 * T.val * M) ^ 2) P)
    (fun n => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_sq]
      convert! (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) T.coe_nonneg) hM)).mpr (hbound n ω) using 1
      rw [sq_abs])
    (Eventually.of_forall fun ω => by
      simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((brownianItoDrift_bounded_tendsto hF hjoint hb hlim T ω).sub_const
          (brownianItoDrift B g T ω)).pow 2)
  simpa only [integral_zero] using hd

theorem brownianItoDriftL2_bounded_tendsto [IsFiniteMeasure P]
    (hF : ∀ n, Measurable (F n)) (hg : Measurable g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hb : ∀ n x, |F n x| ≤ M) (hbg : ∀ x, |g x| ≤ M)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (g x))) (T : ℝ≥0) :
    Tendsto (fun n => brownianItoDriftL2 B (F n) T
      (brownianItoDrift_bounded_memLp (P := P) (hF n) hjoint (hb n) T)) atTop
      (𝓝 (brownianItoDriftL2 B g T (brownianItoDrift_bounded_memLp (P := P) hg hjoint hbg T))) := by
  let A (n : ℕ) := brownianItoDriftL2 B (F n) T (brownianItoDrift_bounded_memLp (P := P) (hF n) hjoint (hb n) T)
  let C := brownianItoDriftL2 B g T (brownianItoDrift_bounded_memLp (P := P) hg hjoint hbg T)
  have he (n : ℕ) : ‖A n - C‖ ^ 2 =
      ∫ ω, (brownianItoDrift B (F n) T ω - brownianItoDrift B g T ω) ^ 2 ∂P := by
    calc
      _ = ∫ ω, (A n - C) ω ^ 2 ∂P := by
        simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp (A n - C))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (A n) C,
          brownianItoDriftL2_coe B (F n) T (brownianItoDrift_bounded_memLp (P := P) (hF n) hjoint (hb n) T),
          brownianItoDriftL2_coe B g T (brownianItoDrift_bounded_memLp (P := P) hg hjoint hbg T)] with ω hd ha hc
        rw [hd, Pi.sub_apply, ha, hc]
  have hs : Tendsto (fun n => ‖A n - C‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using brownianItoDrift_bounded_secondMoment_tendsto hF hg hjoint hb hbg hlim T
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
