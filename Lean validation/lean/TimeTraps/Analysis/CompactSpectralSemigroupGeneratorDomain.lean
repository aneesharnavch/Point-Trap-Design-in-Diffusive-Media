module

public import TimeTraps.Analysis.CompactSpectralSemigroupContinuity
public import TimeTraps.Analysis.CompactInverseDomainCharacterization

@[expose] public section

/-! The spectral heat operators preserve the domain of the actual inverse
operator and commute with it.  A real-time curve is introduced for right
derivatives at zero; its negative-time extension is constant. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.heatSemigroup_commutes {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (x : E) :
    T (h.heatSemigroup t x) = h.heatSemigroup t (T x) := by
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, h.inner_eigenbasis_apply, h.heatSemigroup_inner]
  ring

theorem CompactPositiveInverse.heatSemigroup_mem_inverse_domain {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (x : (inverseOperator T h.injective).domain) :
    h.heatSemigroup t (x : E) ∈ (inverseOperator T h.injective).domain := by
  refine ⟨h.heatSemigroup t (inverseOperator T h.injective x), ?_⟩
  change T (h.heatSemigroup t (inverseOperator T h.injective x)) = _
  rw [h.heatSemigroup_commutes, inverseOperator_right_inverse]

theorem CompactPositiveInverse.inverse_heatSemigroup {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (t : ℝ≥0) (x : (inverseOperator T h.injective).domain) :
    inverseOperator T h.injective
      ⟨h.heatSemigroup t (x : E), h.heatSemigroup_mem_inverse_domain t x⟩ =
        h.heatSemigroup t (inverseOperator T h.injective x) := by
  apply h.injective
  rw [inverseOperator_right_inverse, h.heatSemigroup_commutes, inverseOperator_right_inverse]

noncomputable def CompactPositiveInverse.heatCurve {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) (t : ℝ) : E := h.heatSemigroup t.toNNReal x

theorem CompactPositiveInverse.heatCurve_inner {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) {t : ℝ} (ht : 0 ≤ t) (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i) (h.heatCurve x t) =
      Real.exp (-t / i.1) * inner ℝ (h.eigenbasis i) x := by
  simp only [CompactPositiveInverse.heatCurve, h.heatSemigroup_inner,
    compactHeatCoefficient, Real.coe_toNNReal t ht]

theorem CompactPositiveInverse.heatCurve_zero {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) : h.heatCurve x 0 = x := by
  simp only [CompactPositiveInverse.heatCurve, Real.toNNReal_zero,
    h.heatSemigroup_zero, ContinuousLinearMap.id_apply]

theorem CompactPositiveInverse.heatCurve_mem_inverse_domain {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain) (t : ℝ) :
    h.heatCurve (x : E) t ∈ (inverseOperator T h.injective).domain :=
  h.heatSemigroup_mem_inverse_domain t.toNNReal x

end TimeTraps.Analysis
