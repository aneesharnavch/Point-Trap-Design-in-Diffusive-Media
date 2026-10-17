module

public import TimeTraps.Analysis.IntervalEnergy
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Absolute continuity of positive-denominator quotients and zero weighted energy. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped BigOperators Topology

theorem interval_absolutelyContinuous_of_dist_le {u v : ℝ → ℝ} {l r C : ℝ}
    (hu : AbsolutelyContinuousOnInterval u l r) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ uIcc l r, ∀ y ∈ uIcc l r,
      dist (v x) (v y) ≤ C * dist (u x) (u y)) :
    AbsolutelyContinuousOnInterval v l r := by
  rw [absolutelyContinuousOnInterval_iff] at hu ⊢
  intro ε hε
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨δ, hδ, hδu⟩ := hu (ε / (C + 1)) (div_pos hε hC1)
  refine ⟨δ, hδ, ?_⟩
  intro I hI hlength
  have hs : (∑ i ∈ Finset.range I.1, dist (v (I.2 i).1) (v (I.2 i).2)) ≤
      C * ∑ i ∈ Finset.range I.1, dist (u (I.2 i).1) (u (I.2 i).2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      hbound _ (hI.1 i hi).1 _ (hI.1 i hi).2
  have hnonneg : 0 ≤ ∑ i ∈ Finset.range I.1, dist (u (I.2 i).1) (u (I.2 i).2) :=
    Finset.sum_nonneg fun _ _ => dist_nonneg
  have ht := (lt_div_iff₀ hC1).mp (hδu I hI hlength)
  nlinarith

theorem inverse_dist_le_of_lower_bound {m a b : ℝ} (hm : 0 < m)
    (hma : m ≤ a) (hmb : m ≤ b) :
    dist a⁻¹ b⁻¹ ≤ (1 / m ^ 2) * dist a b := by
  have ha := hm.trans_le hma
  have hb := hm.trans_le hmb
  have hprod : m ^ 2 ≤ a * b := by
    simpa only [pow_two] using mul_le_mul hma hmb hm.le ha.le
  calc
    dist a⁻¹ b⁻¹ = |a - b| / (a * b) := by
      rw [Real.dist_eq, inv_sub_inv (ne_of_gt ha) (ne_of_gt hb), abs_div,
        abs_mul, abs_of_pos ha, abs_of_pos hb, abs_sub_comm]
    _ ≤ |a - b| / m ^ 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hm) hprod
    _ = (1 / m ^ 2) * dist a b := by rw [Real.dist_eq]; ring

theorem interval_absolutelyContinuous_inv {u : ℝ → ℝ} {l r : ℝ}
    (hu : AbsolutelyContinuousOnInterval u l r)
    (hpos : ∀ x ∈ uIcc l r, 0 < u x) :
    AbsolutelyContinuousOnInterval (fun x => (u x)⁻¹) l r := by
  obtain ⟨m, hm, hbound⟩ := isCompact_uIcc.exists_forall_le' hu.continuousOn hpos
  apply interval_absolutelyContinuous_of_dist_le hu
    (show 0 ≤ 1 / m ^ 2 from one_div_nonneg.mpr (sq_nonneg m))
  intro x hx y hy
  exact inverse_dist_le_of_lower_bound hm (hbound x hx) (hbound y hy)

theorem interval_absolutelyContinuous_div {u v : ℝ → ℝ} {l r : ℝ}
    (hu : AbsolutelyContinuousOnInterval u l r)
    (hv : AbsolutelyContinuousOnInterval v l r)
    (hpos : ∀ x ∈ uIcc l r, 0 < v x) :
    AbsolutelyContinuousOnInterval (fun x => u x / v x) l r := by
  simpa only [div_eq_mul_inv] using
    hu.fun_mul (interval_absolutelyContinuous_inv hv hpos)

theorem interval_absolutelyContinuous_constant_of_weighted_derivative_zero
    {u a : ℝ → ℝ} {l r : ℝ}
    (hu : AbsolutelyContinuousOnInterval u l r) (hlr : l ≤ r)
    (hapos : ∀ x ∈ Icc l r, 0 < a x)
    (hi : IntervalIntegrable (fun x => a x * deriv u x ^ 2) volume l r)
    (hzero : (∫ x in l..r, a x * deriv u x ^ 2) = 0) :
    ∀ x ∈ Icc l r, u x = u l := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc l r)] (fun x => a x * deriv u x ^ 2) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun x hx =>
      mul_nonneg (hapos x ⟨hx.1.le, hx.2⟩).le (sq_nonneg _)
  have hz := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hlr hnonneg hi).mp hzero
  have hzcc : (fun x => a x * deriv u x ^ 2) =ᵐ[volume.restrict (Icc l r)] 0 := by
    rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hz
  have hderivzero : ∀ᵐ x, x ∈ uIcc l r → HasDerivAt u 0 x := by
    have hz' := (ae_restrict_iff' measurableSet_Icc).mp hzcc
    filter_upwards [hu.ae_differentiableAt, hz'] with x hx hz hxmem
    have hxI : x ∈ Icc l r := by simpa only [uIcc_of_le hlr] using hxmem
    have hsq : deriv u x ^ 2 = 0 :=
      (mul_eq_zero.mp (hz hxI)).resolve_left (ne_of_gt (hapos x hxI))
    simpa only [sq_eq_zero_iff.mp hsq] using (hx hxmem).hasDerivAt
  obtain ⟨c, hc⟩ := hu.const_of_ae_hasDerivAt_zero hderivzero
  intro x hx
  exact (hc x (by simpa only [uIcc_of_le hlr] using hx)).trans (hc l left_mem_uIcc).symm

end TimeTraps.Analysis
