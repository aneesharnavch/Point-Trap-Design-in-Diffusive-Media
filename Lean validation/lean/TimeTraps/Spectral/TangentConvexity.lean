module

public import TimeTraps.Spectral.ArctanConcavity

@[expose] public section

/-! Exact tangent-half calculus and strict Jensen for positive phase jumps. -/

namespace TimeTraps.Spectral

open Set Filter
open scoped BigOperators Topology

noncomputable def tangentHalf (t : ℝ) : ℝ := Real.tan (t / 2)

noncomputable def tangentHalfSlope (t : ℝ) : ℝ := (1 / 2) / Real.cos (t / 2) ^ 2

theorem tangentHalf_branch {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    t / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor <;> linarith [ht.1, ht.2, Real.pi_pos]

theorem tangentHalf_hasDerivAt {t : ℝ} (hc : Real.cos (t / 2) ≠ 0) :
    HasDerivAt tangentHalf (tangentHalfSlope t) t := by
  have h := (Real.hasDerivAt_tan hc).comp t ((hasDerivAt_id t).div_const 2)
  change HasDerivAt tangentHalf ((1 / Real.cos (t / 2) ^ 2) * (1 / 2)) t at h
  convert h using 1
  unfold tangentHalfSlope
  ring

theorem tangentHalfSlope_hasDerivAt {t : ℝ} (hc : Real.cos (t / 2) ≠ 0) :
    HasDerivAt tangentHalfSlope
      (Real.sin (t / 2) / (2 * Real.cos (t / 2) ^ 3)) t := by
  have hg := ((hasDerivAt_id t).div_const 2).cos
  have h := (hasDerivAt_const t (1 / 2 : ℝ)).div (hg.pow 2) (pow_ne_zero 2 hc)
  change HasDerivAt tangentHalfSlope
    ((0 * Real.cos (t / 2) ^ 2 -
      (1 / 2) * (2 * Real.cos (t / 2) ^ (2 - 1) * (-Real.sin (t / 2) * (1 / 2)))) /
      (Real.cos (t / 2) ^ 2) ^ 2) t at h
  convert h using 1
  field_simp [hc]
  ring

theorem tangentHalf_deriv_two {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    deriv^[2] tangentHalf t = Real.sin (t / 2) / (2 * Real.cos (t / 2) ^ 3) := by
  have he : deriv tangentHalf =ᶠ[𝓝 t] tangentHalfSlope := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (tangentHalf_hasDerivAt (ne_of_gt
      (Real.cos_pos_of_mem_Ioo (tangentHalf_branch hx)))).deriv
  change deriv (deriv tangentHalf) t = _
  rw [he.deriv_eq]
  exact (tangentHalfSlope_hasDerivAt
    (ne_of_gt (Real.cos_pos_of_mem_Ioo (tangentHalf_branch ht)))).deriv

theorem tangentHalf_deriv_two_factor {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    deriv^[2] tangentHalf t =
      (1 / 2) * (1 / Real.cos (t / 2) ^ 2) * Real.tan (t / 2) := by
  rw [tangentHalf_deriv_two ht, Real.tan_eq_sin_div_cos]
  have hc := ne_of_gt (Real.cos_pos_of_mem_Ioo (tangentHalf_branch ht))
  field_simp [hc]

theorem tangentHalf_deriv_two_pos {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    0 < deriv^[2] tangentHalf t := by
  rw [tangentHalf_deriv_two ht]
  have hc := Real.cos_pos_of_mem_Ioo (tangentHalf_branch ht)
  have hs : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  exact div_pos hs (mul_pos (by norm_num) (pow_pos hc 3))

theorem tangentHalf_strictConvexOn :
    StrictConvexOn ℝ (Ioo 0 Real.pi) tangentHalf := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioo 0 Real.pi)
  · intro t ht
    exact (tangentHalf_hasDerivAt
      (ne_of_gt (Real.cos_pos_of_mem_Ioo (tangentHalf_branch ht)))).continuousAt.continuousWithinAt
  · intro t ht
    exact tangentHalf_deriv_two_pos ht

theorem tangentHalf_sum_ge {n : ℕ} (hn : 0 < n)
    (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Ioo 0 Real.pi) :
    n * tangentHalf ((∑ i, t i) / n) ≤ ∑ i, tangentHalf (t i) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hw : (∑ _i : Fin n, (n : ℝ)⁻¹) = 1 := by simp [ne_of_gt hn']
  have h := tangentHalf_strictConvexOn.convexOn.map_sum_le
    (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := t)
    (fun _ _ => le_of_lt (inv_pos.mpr hn')) hw (fun i _ => ht i)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  have hm : (n : ℝ)⁻¹ * ∑ i, t i = (∑ i, t i) / n := by ring
  rw [hm] at h
  have := mul_le_mul_of_nonneg_left h hn'.le
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn'), one_mul] using this

theorem tangentHalf_sum_eq_iff {n : ℕ} (hn : 0 < n)
    (t : Fin n → ℝ) (ht : ∀ i, t i ∈ Ioo 0 Real.pi) :
    (∑ i, tangentHalf (t i)) = n * tangentHalf ((∑ i, t i) / n) ↔
      ∀ i, t i = (∑ j, t j) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hw : (∑ _i : Fin n, (n : ℝ)⁻¹) = 1 := by simp [ne_of_gt hn']
  have h := tangentHalf_strictConvexOn.map_sum_eq_iff
    (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := t)
    (fun _ _ => inv_pos.mpr hn') hw (fun i _ => ht i)
  simp only [smul_eq_mul, ← Finset.mul_sum, Finset.mem_univ, forall_true_left] at h
  have hm : (n : ℝ)⁻¹ * ∑ i, t i = (∑ i, t i) / n := by ring
  rw [hm] at h
  rw [← h]
  constructor
  · intro he
    rw [he]
    field_simp
  · intro he
    rw [he]
    field_simp

end TimeTraps.Spectral
