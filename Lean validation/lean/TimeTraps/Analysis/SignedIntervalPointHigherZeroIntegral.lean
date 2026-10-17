module

public import TimeTraps.Analysis.IntervalPointForm
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! A continuous function orthogonal to a strictly positive continuous
weight has a zero in the open interval. Only positivity in the interior
is needed; no endpoint sign or differentiability is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem exists_interior_zero_of_weighted_integral_eq_zero
    {l r : ℝ} (hlr : l < r) {u w : ℝ → ℝ}
    (hu : ContinuousOn u (Icc l r)) (hw : ContinuousOn w (Icc l r))
    (hwpos : ∀ x ∈ Ioo l r, 0 < w x)
    (hzero : (∫ x in l..r, u x * w x) = 0) :
    ∃ x ∈ Ioo l r, u x = 0 := by
  by_contra hn
  have hne : ∀ x ∈ Ioo l r, u x ≠ 0 := by
    intro x hx hz
    exact hn ⟨x, hx, hz⟩
  have hint : IntervalIntegrable (fun x => u x * w x) volume l r :=
    (hu.mul hw).intervalIntegrable_of_Icc hlr.le
  rcases isPreconnected_Ioo.mapsTo_Ioi_or_Iio
      (hu.mono Ioo_subset_Icc_self) hne with hpos | hneg
  · have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hint
      (fun x hx => mul_pos (hpos hx) (hwpos x hx)) hlr
    exact hp.ne' hzero
  · have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hint.neg
      (fun x hx => neg_pos.mpr (mul_neg_of_neg_of_pos (hneg hx) (hwpos x hx))) hlr
    change 0 < ∫ x in l..r, -(u x * w x) at hp
    rw [intervalIntegral.integral_neg, hzero, neg_zero] at hp
    exact lt_irrefl 0 hp

end TimeTraps.Analysis
