module

public import TimeTraps.Analysis.IntervalEnergyCoercive

@[expose] public section

/-! The physical point-contact form on an arbitrary finite interval.
Its restrictions to energy representatives are independent of exterior
extensions, and the existing unit-interval form is its exact specialization. -/

namespace TimeTraps.Analysis

open Set MeasureTheory
open scoped BigOperators

noncomputable def intervalPointForm {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (l r : ℝ) (u v : ℝ → ℝ) : ℝ :=
  D * (∫ x in l..r, deriv u x * deriv v x) + ∑ i, κ i * u (z i) * v (z i)

theorem intervalPointForm_self {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (l r : ℝ) (u : ℝ → ℝ) :
    intervalPointForm D κ z l r u u =
      D * (∫ x in l..r, deriv u x ^ 2) + ∑ i, κ i * u (z i) ^ 2 := by
  simp only [intervalPointForm, pow_two, mul_assoc]

theorem intervalPointForm_lower_single {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (l r : ℝ) (hκ : ∀ i, 0 ≤ κ i) (u : ℝ → ℝ) (k : ι) :
    D * (∫ x in l..r, deriv u x ^ 2) + κ k * u (z k) ^ 2 ≤
      intervalPointForm D κ z l r u u := by
  classical
  rw [intervalPointForm_self]
  exact add_le_add le_rfl
    (Finset.single_le_sum (fun i _ => mul_nonneg (hκ i) (sq_nonneg (u (z i)))) (Finset.mem_univ k))

theorem intervalPointForm_congr {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) {l r : ℝ} (hlr : l ≤ r) (hz : ∀ i, z i ∈ Icc l r)
    {u v w f : ℝ → ℝ} (huv : EqOn u v (Icc l r)) (hwf : EqOn w f (Icc l r)) :
    intervalPointForm D κ z l r u w = intervalPointForm D κ z l r v f := by
  unfold intervalPointForm
  congr 1
  · congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le hlr
    intro x hx
    change deriv u x * deriv w x = deriv v x * deriv f x
    rw [(huv.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx,
      (hwf.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx]
  · apply Finset.sum_congr rfl
    intro i _
    rw [huv (hz i), hwf (hz i)]

theorem intervalPointForm_unit {ι : Type*} [Fintype ι]
    (D : ℝ) (κ z : ι → ℝ) (u v : ℝ → ℝ) :
    intervalPointForm D κ z 0 1 u v = unitPointForm D κ z u v := rfl

end TimeTraps.Analysis
