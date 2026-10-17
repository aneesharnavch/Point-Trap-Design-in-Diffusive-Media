module

public import TimeTraps.Analysis.IntegralCauchySchwarz
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Dominated convergence in the actual real L2 norm. This supplies the
closed-space step in predictable density without any path continuity. -/

namespace TimeTraps.Probability

open MeasureTheory Filter TimeTraps.Analysis
open scoped Topology ENNReal

theorem brownianPredictableDensity_toLp_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g H : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ) (hH : MemLp H 2 μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ H x) (hgb : ∀ᵐ x ∂μ, |g x| ≤ H x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hbound : Integrable (fun x => (2 * H x) ^ 2) μ := by
    simpa only [mul_pow] using hH.integrable_sq.const_mul ((2 : ℝ) ^ 2)
  have hd := tendsto_integral_of_dominated_convergence
    (F := fun n x => (f n x - g x) ^ 2) (f := fun _ => (0 : ℝ)) (fun x => (2 * H x) ^ 2)
    (fun n => (((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)) hbound
    (fun n => by
      filter_upwards [hb n, hgb] with x hfx hgx
      have ha : |f n x - g x| ≤ 2 * H x := (abs_sub _ _).trans (by linarith)
      have hp : 0 ≤ 2 * H x := (abs_nonneg _).trans ha
      rw [Real.norm_eq_abs, abs_sq]
      have hh := mul_self_le_mul_self (abs_nonneg _) ha
      nlinarith [sq_abs (f n x - g x)])
    (hlim.mono (fun x hx => by
      simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using (hx.sub_const (g x)).pow 2))
  have he (n : ℕ) : ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 =
      ∫ x, (f n x - g x) ^ 2 ∂μ := by
    calc
      _ = ∫ x, ((hf n).toLp (f n) - hg.toLp g) x ^ 2 ∂μ := by
        simpa only [Lp.toLp_coeFn] using
          memLp_norm_toLp_sq (Lp.memLp ((hf n).toLp (f n) - hg.toLp g))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
          (hf n).coeFn_toLp, hg.coeFn_toLp] with x hsub hfn hgn
        rw [hsub, Pi.sub_apply, hfn, hgn]
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he, integral_zero] using hd
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
