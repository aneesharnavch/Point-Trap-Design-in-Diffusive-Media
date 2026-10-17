module

public import TimeTraps.Analysis.GraphHeatPointKernelLaplaceData
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-! The direct Laplace integral of the singular actual graph point
kernel equals the discounted finite-time point potential. The derivative
is used only at positive times, and both endpoint terms are justified. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_hasDerivAt
    (P : GraphShiftedContactOperatorProblem V E) (x a : GraphRealization P.geometry)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (P.realizedHeatPointPotential x a) (P.realizedHeatPointKernelTime x a t) t := by
  obtain ⟨_, _, hb⟩ := P.realizedHeatPointPotential_global_bound
  have hc := P.realizedHeatPointKernelTime_continuousOn x a
  exact intervalIntegral.integral_hasDerivAt_right (hb t ht.le x a).1
    (hc.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hc.continuousAt (isOpen_Ioi.mem_nhds ht))

theorem GraphShiftedContactOperatorProblem.pointKernelLaplaceOne_eq
    (P : GraphShiftedContactOperatorProblem V E) (x a : GraphRealization P.geometry) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) * P.realizedHeatPointKernelTime x a t) =
      P.pointLocalTimeDiscountedPotential a 1 x := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt
      (fun r => Real.exp (-r) * P.realizedHeatPointPotential x a r)
      (Real.exp (-t) * P.realizedHeatPointKernelTime x a t -
        Real.exp (-t) * P.realizedHeatPointPotential x a t) t := by
    intro t ht
    simpa only [Pi.mul_def, Pi.neg_apply, id_eq, mul_neg_one, neg_mul, sub_eq_add_neg, add_comm] using
      (((hasDerivAt_id t).neg.exp).mul (P.realizedHeatPointPotential_hasDerivAt x a ht))
  have hp : Continuous (fun t : ℝ => ((x, a), t)) := continuous_const.prodMk continuous_id
  have hU := P.realizedHeatPointPotential_joint_continuous.comp hp
  have he : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
  have hc := he.mul hU
  have hA : IntegrableOn (fun t : ℝ => Real.exp (-t) * P.realizedHeatPointPotential x a t) (Ioi 0) := by
    simpa only [one_mul] using P.pointLocalTimeDiscountedPotential_integrable a x (q := 1) (by norm_num)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousAt.continuousWithinAt hd
    ((P.pointKernelLaplaceOne_integrable x a).sub hA) (P.pointPotentialLaplaceOne_tendsto x a)
  rw [integral_sub (P.pointKernelLaplaceOne_integrable x a) hA] at h
  change (∫ t in Ioi (0 : ℝ), Real.exp (-t) * P.realizedHeatPointKernelTime x a t) -
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) * P.realizedHeatPointPotential x a t) =
        0 - Real.exp (-(0 : ℝ)) * P.realizedHeatPointPotential x a 0 at h
  have hz : P.realizedHeatPointPotential x a 0 = 0 := by
    simp only [realizedHeatPointPotential, intervalIntegral.integral_same]
  rw [hz, mul_zero, sub_zero] at h
  have heq := sub_eq_zero.mp h
  simpa only [pointLocalTimeDiscountedPotential, one_mul] using heq

end TimeTraps.Analysis
