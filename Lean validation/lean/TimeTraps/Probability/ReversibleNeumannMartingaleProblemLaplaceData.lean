module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemDynkin
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-! The scalar discounted Dynkin identity follows from ordinary
calculus and boundedness. It will be applied to expectations of test
values and generators; no stochastic uniqueness principle is used. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped Topology

theorem boundedDynkin_discounted_integrable {u : ℝ → ℝ} (hu : Continuous u)
    {M : ℝ} (hb : ∀ t, ‖u t‖ ≤ M) {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t => Real.exp (-α * t) * u t) (Ioi (0 : ℝ)) := by
  apply ((exp_neg_integrableOn_Ioi 0 hα).mul_const M).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hu).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  change ‖Real.exp (-α * t) * u t‖ ≤ Real.exp (-α * t) * M
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le

theorem boundedDynkin_discounted_tendsto_zero {u : ℝ → ℝ}
    {M : ℝ} (hb : ∀ t, ‖u t‖ ≤ M) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun t => Real.exp (-α * t) * u t) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-α * t)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun t : ℝ => α * t) atTop atTop := tendsto_id.const_mul_atTop hα
    have h : Tendsto (fun t : ℝ => Real.exp (-(α * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hbase
    have heq : (fun t : ℝ => Real.exp (-(α * t))) = (fun t => Real.exp (-α * t)) := by
      funext t
      rw [neg_mul]
    exact heq ▸ h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun t => ?_))
    (by simpa only [zero_mul] using he.mul_const M)
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le

theorem boundedDynkin_laplace_identity {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {M N : ℝ}
    (hub : ∀ t, ‖u t‖ ≤ M) (hvb : ∀ t, ‖v t‖ ≤ N)
    (hdyn : ∀ T, 0 ≤ T → u T = u 0 + ∫ r in (0 : ℝ)..T, v r)
    {α : ℝ} (hα : 0 < α) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * (α * u t - v t)) = u 0 := by
  have hud (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt u (v t) t := by
    have hi := (intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
      hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt).const_add (u 0)
    apply hi.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact hdyn s hs.le
  have hfd (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun s => Real.exp (-α * s) * u s)
        (Real.exp (-α * t) * (v t - α * u t)) t := by
    convert! (((hasDerivAt_id t).const_mul (-α)).exp.mul (hud t ht)) using 1
    simp only [id_eq]
    ring
  have hcont : Continuous (fun t => Real.exp (-α * t) * u t) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hu
  have hw : ∀ t, ‖v t - α * u t‖ ≤ N + |α| * M := by
    intro t
    exact (norm_sub_le _ _).trans (add_le_add (hvb t) (by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hub t) (abs_nonneg α)))
  have hi := boundedDynkin_discounted_integrable (hv.sub (continuous_const.mul hu)) hw hα
  have he := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousAt.continuousWithinAt
    hfd hi (boundedDynkin_discounted_tendsto_zero hub hα)
  have hneg : (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * (v t - α * u t)) =
      -(∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * (α * u t - v t)) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), -(Real.exp (-α * t) * (α * u t - v t)) :=
        integral_congr_ae (Eventually.of_forall (fun t => by ring))
      _ = _ := integral_neg _
  simp only [mul_zero, Real.exp_zero, one_mul, zero_sub] at he
  linarith

end TimeTraps.Probability

end
