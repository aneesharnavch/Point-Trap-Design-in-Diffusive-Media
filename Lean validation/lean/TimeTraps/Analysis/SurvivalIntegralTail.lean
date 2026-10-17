module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

/-! A nonnegative nonincreasing survival function with uniformly bounded
finite-horizon integrals tends to zero, with the explicit C/T bound.
Monotonicity supplies local integrability; continuity is unnecessary.
These are generic analytic implications, not assumptions about any
particular stochastic survival process. -/

namespace TimeTraps.Analysis

open MeasureTheory Set Filter
open scoped NNReal Topology

theorem survivalIntegralTail_intervalIntegrable {w : ℝ≥0 → ℝ}
    (hw : Antitone w) (T : ℝ≥0) :
    IntervalIntegrable (fun r : ℝ => w r.toNNReal) volume 0 T.val :=
  (hw.comp_monotone Real.toNNReal_monotone).intervalIntegrable

theorem survivalIntegralTail_mul_le_integral {w : ℝ≥0 → ℝ}
    (hw : Antitone w) (T : ℝ≥0) :
    T.val * w T ≤ ∫ r in (0 : ℝ)..T.val, w r.toNNReal := by
  calc
    _ = ∫ _r in (0 : ℝ)..T.val, w T := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    _ ≤ _ := intervalIntegral.integral_mono_on T.coe_nonneg intervalIntegrable_const
      (survivalIntegralTail_intervalIntegrable hw T)
      (fun r hr => hw (Real.toNNReal_le_iff_le_coe.mpr hr.2))

theorem survivalIntegralTail_mul_le {w : ℝ≥0 → ℝ} (hw : Antitone w) {C : ℝ}
    (hC : ∀ T : ℝ≥0, (∫ r in (0 : ℝ)..T.val, w r.toNNReal) ≤ C) (T : ℝ≥0) :
    T.val * w T ≤ C :=
  (survivalIntegralTail_mul_le_integral hw T).trans (hC T)

theorem survivalIntegralTail_le_div {w : ℝ≥0 → ℝ} (hw : Antitone w) {C : ℝ}
    (hC : ∀ T : ℝ≥0, (∫ r in (0 : ℝ)..T.val, w r.toNNReal) ≤ C)
    {T : ℝ≥0} (hT : 0 < T) :
    w T ≤ C / T.val := by
  apply (le_div_iff₀ (show 0 < T.val from hT)).mpr
  simpa only [mul_comm] using survivalIntegralTail_mul_le hw hC T

theorem survivalIntegralTail_tendsto {w : ℝ≥0 → ℝ} (hw : Antitone w)
    (hn : ∀ T, 0 ≤ w T) {C : ℝ}
    (hC : ∀ T : ℝ≥0, (∫ r in (0 : ℝ)..T.val, w r.toNNReal) ≤ C) :
    Tendsto w atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ≥0 => T.val) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hd : Tendsto (fun T : ℝ≥0 => C / T.val) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp ht).const_mul C
  apply squeeze_zero' (Eventually.of_forall hn) _ hd
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with T hT
  exact survivalIntegralTail_le_div hw hC hT

theorem survivalIntegralTail_residual_tendsto {w : ℝ≥0 → ℝ} (hw : Antitone w)
    (hn : ∀ T, 0 ≤ w T) {C : ℝ}
    (hC : ∀ T : ℝ≥0, (∫ r in (0 : ℝ)..T.val, w r.toNNReal) ≤ C)
    {r : ℝ≥0 → ℝ} {M : ℝ} (hr : ∀ T, |r T| ≤ M * w T) :
    Tendsto r atTop (𝓝 0) := by
  have hb : Tendsto (fun T => M * w T) atTop (𝓝 0) := by
    simpa only [mul_zero] using (survivalIntegralTail_tendsto hw hn hC).const_mul M
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun T => abs_nonneg (r T)) hr hb

end TimeTraps.Analysis
