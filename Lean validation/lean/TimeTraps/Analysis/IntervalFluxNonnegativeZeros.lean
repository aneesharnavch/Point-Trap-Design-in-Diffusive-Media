module

public import TimeTraps.Analysis.IntervalSturmCauchyUniqueness
public import TimeTraps.Analysis.IntervalEndpointMinimumDerivative
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Local zeros and endpoint signs of a nonnegative state are expressed
in the original physical flux. Interior zeros supply zero Cauchy data;
endpoint signs point into the interval because the conductance is positive. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology

theorem IntervalFluxRegularity.flux_zero_of_nonnegative_interior_zero
    {u j g p : ℝ → ℝ} {a b x : ℝ} (h : IntervalFluxRegularity u j g p a b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ y ∈ Icc a b, 0 < p y)
    (hn : ∀ y ∈ Icc a b, 0 ≤ u y) (hx : x ∈ Ioo a b) (hz : u x = 0) : j x = 0 := by
  have hmin : IsLocalMin u x := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
    rw [hz]
    exact hn y hy
  have hd := hmin.hasDerivAt_eq_zero (h.hasDerivAt hp (fun y hy => (hpos y hy).ne') hx)
  exact (div_eq_zero_iff.mp hd).resolve_right (hpos x (Ioo_subset_Icc_self hx)).ne'

theorem IntervalFluxRegularity.eq_zero_of_nonnegative_interior_zero
    {u j p c : ℝ → ℝ} {a b x : ℝ}
    (h : IntervalFluxRegularity u j (fun y => c y * u y) p a b)
    (hp : ContinuousOn p (Icc a b)) (hpos : ∀ y ∈ Icc a b, 0 < p y)
    (hc : ContinuousOn c (Icc a b)) (hn : ∀ y ∈ Icc a b, 0 ≤ u y)
    (hx : x ∈ Ioo a b) (hz : u x = 0) : ∀ y ∈ Icc a b, u y = 0 ∧ j y = 0 :=
  h.eq_zero_of_linear_cauchy hp hpos hc (hx.1.trans hx.2).le (Ioo_subset_Icc_self hx) hz
    (h.flux_zero_of_nonnegative_interior_zero hp hpos hn hx hz)

theorem IntervalFluxRegularity.left_flux_nonneg_of_nonnegative_zero
    {u j g p : ℝ → ℝ} {a b : ℝ} (h : IntervalFluxRegularity u j g p a b)
    (hab : a < b) (hp : ContinuousOn p (Icc a b)) (hpos : ∀ y ∈ Icc a b, 0 < p y)
    (hn : ∀ y ∈ Icc a b, 0 ≤ u y) (hz : u a = 0) : 0 ≤ j a := by
  have hpa := hpos a ⟨le_rfl, hab.le⟩
  have hd := interval_nonnegative_left_derivative hab hn hz
    (h.hasDerivWithinAt_left hab hp (fun y hy => (hpos y hy).ne'))
  have hm := mul_nonneg hd hpa.le
  simpa only [div_mul_cancel₀ _ hpa.ne'] using hm

theorem IntervalFluxRegularity.right_flux_nonpos_of_nonnegative_zero
    {u j g p : ℝ → ℝ} {a b : ℝ} (h : IntervalFluxRegularity u j g p a b)
    (hab : a < b) (hp : ContinuousOn p (Icc a b)) (hpos : ∀ y ∈ Icc a b, 0 < p y)
    (hn : ∀ y ∈ Icc a b, 0 ≤ u y) (hz : u b = 0) : j b ≤ 0 := by
  have hpb := hpos b ⟨hab.le, le_rfl⟩
  have hd := interval_nonnegative_right_derivative hab hn hz
    (h.hasDerivWithinAt_right hab hp (fun y hy => (hpos y hy).ne'))
  have hm := mul_nonpos_of_nonpos_of_nonneg hd hpb.le
  simpa only [div_mul_cancel₀ _ hpb.ne'] using hm

end TimeTraps.Analysis
