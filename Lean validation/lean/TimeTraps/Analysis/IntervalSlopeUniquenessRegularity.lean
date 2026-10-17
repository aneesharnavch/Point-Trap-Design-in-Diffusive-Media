module

public import TimeTraps.Analysis.IntervalPointRegularityData
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section

/-! One-sided derivatives of actual energy representatives, and the
classical slope equation derived when the second derivative is a real
constant times the continuous state. No extra regularity is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

theorem intervalEnergy_hasDerivWithinAt_left_of_ae_deriv
    {u v : ℝ → ℝ} {a b : ℝ} (hu : IntervalEnergy u a b) (hab : a < b)
    (hv : ContinuousOn v (Icc a b))
    (hd : deriv u =ᵐ[volume.restrict (Ioo a b)] v) :
    HasDerivWithinAt u (v a) (Ici a) a := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo a b)
    (fun x hx => (intervalEnergy_hasDerivAt_of_ae_deriv hu hv hd hx).differentiableAt.differentiableWithinAt)
    ((hu.continuousOn a left_mem_uIcc).mono ?_) (Ioo_mem_nhdsGT hab)
    (intervalEnergy_deriv_left_trace hu hab hv hd)
  rw [uIcc_of_le hab.le]
  exact Ioo_subset_Icc_self

theorem intervalEnergy_hasDerivWithinAt_right_of_ae_deriv
    {u v : ℝ → ℝ} {a b : ℝ} (hu : IntervalEnergy u a b) (hab : a < b)
    (hv : ContinuousOn v (Icc a b))
    (hd : deriv u =ᵐ[volume.restrict (Ioo a b)] v) :
    HasDerivWithinAt u (v b) (Iic b) b := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Ioo a b)
    (fun x hx => (intervalEnergy_hasDerivAt_of_ae_deriv hu hv hd hx).differentiableAt.differentiableWithinAt)
    ((hu.continuousOn b right_mem_uIcc).mono ?_) (Ioo_mem_nhdsLT hab)
    (intervalEnergy_deriv_right_trace hu hab hv hd)
  rw [uIcc_of_le hab.le]
  exact Ioo_subset_Icc_self

theorem IntervalSlopeRegularity.linear_slope_hasDerivAt
    {u j : ℝ → ℝ} {c a b : ℝ}
    (h : IntervalSlopeRegularity u j (fun x => c * u x) a b)
    {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt j (c * u x) x := by
  apply intervalEnergy_hasDerivAt_of_ae_deriv h.slope_energy _ h.second_ae hx
  exact continuousOn_const.mul (by
    simpa only [uIcc_of_le (hx.1.trans hx.2).le] using h.state_energy.continuousOn)

end TimeTraps.Analysis
