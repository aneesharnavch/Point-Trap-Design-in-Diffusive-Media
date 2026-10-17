module

public import TimeTraps.Analysis.GraphHeatPointResolventRegularity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-! Exponential integrability of the genuine point kernel allows its
integrable square-root singularity at zero. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem graphPointKernelDiscount_envelope_integrable :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * (1 + 1 / Real.sqrt t)) (Ioi 0) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  have hr : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-t)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2)) (b := 1)
        (by norm_num) (by norm_num) (by norm_num)
  apply (he.add hr).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ht.le
  simp only [Pi.add_apply, Real.rpow_neg ht0, Real.sqrt_eq_rpow]
  ring

theorem GraphShiftedContactOperatorProblem.pointKernelLaplaceOne_integrable
    (P : GraphShiftedContactOperatorProblem V E) (x a : GraphRealization P.geometry) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * P.realizedHeatPointKernelTime x a t) (Ioi 0) := by
  obtain ⟨C, _, hb⟩ := P.realizedHeatKernel_global_bound
  have he : Measurable (fun t : ℝ => Real.exp (-t)) := by fun_prop
  have hm := he.mul (P.realizedHeatPointKernelTime_measurable x a)
  apply (graphPointKernelDiscount_envelope_integrable.const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  change ‖Real.exp (-t) * P.realizedHeatPointKernelTime x a t‖ ≤ C * (Real.exp (-t) * (1 + 1 / Real.sqrt t))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (P.realizedHeatPointKernelTime_nonneg x a t))]
  have hk : P.realizedHeatPointKernelTime x a t ≤ C * (1 + 1 / Real.sqrt t) := by
    unfold realizedHeatPointKernelTime
    rw [dif_pos ht0]
    simpa only [Real.coe_toNNReal t ht0.le] using
      (hb t.toNNReal (Real.toNNReal_pos.mpr ht0) x a).2
  nlinarith [mul_le_mul_of_nonneg_left hk (Real.exp_pos (-t)).le]

theorem GraphShiftedContactOperatorProblem.pointPotentialLaplaceOne_tendsto
    (P : GraphShiftedContactOperatorProblem V E) (x a : GraphRealization P.geometry) :
    Tendsto (fun t : ℝ => Real.exp (-t) * P.realizedHeatPointPotential x a t) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := P.realizedHeatPointPotential_global_bound
  have hlim : Tendsto (fun t : ℝ => Real.exp (-t) * (3 * C * t)) atTop (𝓝 0) := by
    simpa only [pow_one, zero_mul, mul_zero, mul_comm, mul_left_comm, mul_assoc] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).mul_const (3 * C)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := by linarith
  have hs : Real.sqrt t ≤ t := by
    have hsq := Real.sq_sqrt ht0
    have hsn := Real.sqrt_nonneg t
    nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hb t ht0 x a).2.1)]
  have hU : P.realizedHeatPointPotential x a t ≤ 3 * C * t := by
    nlinarith [(hb t ht0 x a).2.2]
  exact mul_le_mul_of_nonneg_left hU (Real.exp_pos _).le

end TimeTraps.Analysis
