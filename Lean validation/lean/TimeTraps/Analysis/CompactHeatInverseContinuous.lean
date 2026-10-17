module

public import TimeTraps.Analysis.CompactSpectralSemigroupSmoothingNorm

@[expose] public section

/-! At positive time the original unbounded inverse composed with heat
evolution is a bounded linear map. Its right-inverse identity and explicit
bound make point evaluation through a Sobolev solution map available. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def CompactPositiveInverse.heatInverseLinear {T : H →L[ℝ] H}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) : H →ₗ[ℝ] H :=
  (inverseOperator T h.injective).toFun.comp
    ((h.heatSemigroup t).toLinearMap.codRestrict (inverseOperator T h.injective).domain
      (h.heatSemigroup_mem_domain_of_pos t ht))

noncomputable def CompactPositiveInverse.heatInverseL {T : H →L[ℝ] H}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) : H →L[ℝ] H :=
  (h.heatInverseLinear t ht).mkContinuous (1 / (t : ℝ)) (fun x => by
    change ‖inverseOperator T h.injective
      ⟨h.heatSemigroup t x, h.heatSemigroup_mem_domain_of_pos t ht x⟩‖ ≤ (1 / (t : ℝ)) * ‖x‖
    simpa only [one_div_mul_eq_div] using h.inverse_heat_norm_le t ht x)

theorem CompactPositiveInverse.heatInverseL_apply {T : H →L[ℝ] H}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) (x : H) :
    h.heatInverseL t ht x = inverseOperator T h.injective
      ⟨h.heatSemigroup t x, h.heatSemigroup_mem_domain_of_pos t ht x⟩ := rfl

theorem CompactPositiveInverse.heatInverseL_right_inverse {T : H →L[ℝ] H}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) (x : H) :
    T (h.heatInverseL t ht x) = h.heatSemigroup t x :=
  inverseOperator_right_inverse T h.injective _

theorem CompactPositiveInverse.heatInverseL_norm_le {T : H →L[ℝ] H}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (ht : 0 < t) :
    ‖h.heatInverseL t ht‖ ≤ 1 / (t : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg zero_le_one ht.le)
  intro x
  change ‖inverseOperator T h.injective
    ⟨h.heatSemigroup t x, h.heatSemigroup_mem_domain_of_pos t ht x⟩‖ ≤ (1 / (t : ℝ)) * ‖x‖
  calc
    _ ≤ ‖x‖ / (t : ℝ) := h.inverse_heat_norm_le t ht x
    _ = _ := by ring

theorem CompactPositiveInverse.heatInverseL_add {T : H →L[ℝ] H}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) :
    h.heatInverseL (s + t) (lt_add_of_lt_of_nonneg hs (show 0 ≤ t from zero_le)) =
      (h.heatInverseL s hs).comp (h.heatSemigroup t) := by
  ext x
  apply h.injective
  rw [h.heatInverseL_right_inverse, ContinuousLinearMap.comp_apply,
    h.heatInverseL_right_inverse, h.heatSemigroup_add]
  rfl

end TimeTraps.Analysis
