module

public import TimeTraps.Analysis.CompactSpectralSemigroup
public import TimeTraps.Analysis.CompactSpectralEnumeration

@[expose] public section

/-! The actual compact heat evolution after removal of its first
enumerated mode. Ordering of every remaining reciprocal eigenvalue is
derived from the constructed enumeration. Parseval gives the second-mode
remainder bound without assuming a strict spectral gap or simplicity. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {T : E →L[ℝ] E}

theorem CompactPositiveInverse.heatSemigroup_eigenbasis
    (h : CompactPositiveInverse T) (t : ℝ≥0) (i : CompactSpectralIndex T) :
    h.heatSemigroup t (h.eigenbasis i) = compactHeatCoefficient t i • h.eigenbasis i := by
  classical
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext j
  simp only [HilbertBasis.repr_apply_apply, h.heatSemigroup_inner, real_inner_smul_right,
    orthonormal_iff_ite.mp h.eigenbasis.orthonormal]
  by_cases hji : j = i
  · subst j
    simp only [ite_true]
  · simp only [hji, ite_false, mul_zero]

variable (h : CompactPositiveInverse T) [Infinite (CompactSpectralIndex T)]

theorem CompactPositiveInverse.second_reciprocal_le_of_ne_first
    (i : CompactSpectralIndex T) (hi : i ≠ h.spectralEnumeration 0) :
    (h.spectralEnumeration 1).1⁻¹ ≤ i.1⁻¹ := by
  have hn : h.spectralEnumeration.symm i ≠ 0 := by
    intro hz
    apply hi
    have he := congrArg h.spectralEnumeration hz
    simpa only [Equiv.apply_symm_apply] using he
  have hm := h.spectralEnumeration_monotone (Nat.one_le_iff_ne_zero.mpr hn)
  simpa only [Equiv.apply_symm_apply] using hm

theorem CompactPositiveInverse.heatSemigroup_orthogonal_first_norm_le
    (t : ℝ≥0) (x : E)
    (hx : inner ℝ (h.eigenbasis (h.spectralEnumeration 0)) x = 0) :
    ‖h.heatSemigroup t x‖ ≤ compactHeatCoefficient t (h.spectralEnumeration 1) * ‖x‖ := by
  have hb (i : CompactSpectralIndex T) :
      (inner ℝ (h.eigenbasis i) (h.heatSemigroup t x)) ^ 2 ≤
        (compactHeatCoefficient t (h.spectralEnumeration 1)) ^ 2 *
          (inner ℝ (h.eigenbasis i) x) ^ 2 := by
    rw [h.heatSemigroup_inner, mul_pow]
    by_cases hi : i = h.spectralEnumeration 0
    · rw [hi, hx, zero_pow (by norm_num : 2 ≠ 0), mul_zero, mul_zero]
    · have hc : compactHeatCoefficient t i ≤ compactHeatCoefficient t (h.spectralEnumeration 1) := by
        apply Real.exp_le_exp.mpr
        have hm := h.second_reciprocal_le_of_ne_first i hi
        change -(t : ℝ) / i.1 ≤ -(t : ℝ) / (h.spectralEnumeration 1).1
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr t.coe_nonneg)
      have hs : (compactHeatCoefficient t i) ^ 2 ≤
          (compactHeatCoefficient t (h.spectralEnumeration 1)) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self (compactHeatCoefficient_pos t i).le hc
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hs := hasSum_le hb (h.hasSum_parseval (h.heatSemigroup t x))
    ((h.hasSum_parseval x).mul_left ((compactHeatCoefficient t (h.spectralEnumeration 1)) ^ 2))
  have he : (compactHeatCoefficient t (h.spectralEnumeration 1)) ^ 2 * ‖x‖ ^ 2 =
      (compactHeatCoefficient t (h.spectralEnumeration 1) * ‖x‖) ^ 2 := (mul_pow _ _ _).symm
  rw [he] at hs
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (compactHeatCoefficient_pos t _).le (norm_nonneg x))).mp hs

theorem CompactPositiveInverse.heatSemigroup_ground_remainder_le (t : ℝ≥0) (x : E) :
    ‖h.heatSemigroup t x -
      (compactHeatCoefficient t (h.spectralEnumeration 0) *
        inner ℝ (h.eigenbasis (h.spectralEnumeration 0)) x) •
          h.eigenbasis (h.spectralEnumeration 0)‖ ≤
      compactHeatCoefficient t (h.spectralEnumeration 1) *
        ‖x - inner ℝ (h.eigenbasis (h.spectralEnumeration 0)) x •
          h.eigenbasis (h.spectralEnumeration 0)‖ := by
  let i := h.spectralEnumeration 0
  have hz : inner ℝ (h.eigenbasis i)
      (x - inner ℝ (h.eigenbasis i) x • h.eigenbasis i) = 0 := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      h.eigenbasis.orthonormal.norm_eq_one, one_pow, mul_one, sub_self]
  have hb := h.heatSemigroup_orthogonal_first_norm_le t
    (x - inner ℝ (h.eigenbasis i) x • h.eigenbasis i) hz
  rw [map_sub, map_smul, h.heatSemigroup_eigenbasis, smul_smul, mul_comm] at hb
  exact hb

end TimeTraps.Analysis
