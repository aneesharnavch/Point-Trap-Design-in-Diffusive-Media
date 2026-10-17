module

public import TimeTraps.Analysis.IntervalEnergyCoercive

@[expose] public section

/-! The physical point form and source functional depend only on the
closed-interval representatives. Exterior extensions are immaterial. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped BigOperators

theorem unitPointForm_congr {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc (0 : ℝ) 1)
    {u v w f : ℝ → ℝ} (huv : EqOn u v (Icc (0 : ℝ) 1))
    (hwf : EqOn w f (Icc (0 : ℝ) 1)) :
    unitPointForm D κ z u w = unitPointForm D κ z v f := by
  have hu' := (huv.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  have hw' := (hwf.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  have hi : (∫ x in (0 : ℝ)..1, deriv u x * deriv w x) =
      ∫ x in (0 : ℝ)..1, deriv v x * deriv f x := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro x hx
    change deriv u x * deriv w x = deriv v x * deriv f x
    rw [hu' hx, hw' hx]
  unfold unitPointForm
  rw [hi]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [huv (hz i), hwf (hz i)]

theorem unitSource_congr {u v : ℝ → ℝ} (huv : EqOn u v (Icc (0 : ℝ) 1)) :
    (∫ x in (0 : ℝ)..1, u x) = ∫ x in (0 : ℝ)..1, v x :=
  intervalIntegral.integral_congr (by simpa only [uIcc_of_le zero_le_one] using huv)

end TimeTraps.Analysis
