module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! One-sided slopes at a zero of a nonnegative interval function have
the inward signs. The proof takes the limit of ordinary secant slopes. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

theorem interval_nonnegative_left_derivative {l r d : ℝ} {u : ℝ → ℝ}
    (hlr : l < r) (hn : ∀ x ∈ Icc l r, 0 ≤ u x) (hz : u l = 0)
    (hd : HasDerivWithinAt u d (Ici l) l) : 0 ≤ d := by
  have ht : Tendsto (slope u l) (𝓝[>] l) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show l ∉ Ioi l by simp)).mp
      (hd.mono Ioi_subset_Ici_self)
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlr)] with x hx hxr
  rw [slope_def_field, hz, sub_zero]
  exact div_nonneg (hn x ⟨hx.le, hxr.le⟩) (sub_pos.mpr hx).le

theorem interval_nonnegative_right_derivative {l r d : ℝ} {u : ℝ → ℝ}
    (hlr : l < r) (hn : ∀ x ∈ Icc l r, 0 ≤ u x) (hz : u r = 0)
    (hd : HasDerivWithinAt u d (Iic r) r) : d ≤ 0 := by
  have ht : Tendsto (slope u r) (𝓝[<] r) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show r ∉ Iio r by simp)).mp
      (hd.mono Iio_subset_Iic_self)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlr)] with x hx hxl
  rw [slope_def_field, hz, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hn x ⟨hxl.le, hx.le⟩) (sub_neg.mpr hx).le

end TimeTraps.Analysis
