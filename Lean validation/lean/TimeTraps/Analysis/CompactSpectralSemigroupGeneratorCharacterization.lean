module

public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorDerivative
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section

/-! The converse generator statement: existence of a strong right derivative
at zero forces membership in the actual inverse domain.  Thus the generator
domain and action are identified exactly, rather than only on a smaller core. -/

namespace TimeTraps.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.heatCurve_right_derivative_coeff {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) {x v : E}
    (hv : HasDerivWithinAt (h.heatCurve x) v (Ici 0) 0) (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i) v = -i.1⁻¹ * inner ℝ (h.eigenbasis i) x := by
  have hc : HasDerivWithinAt (fun t => inner ℝ (h.eigenbasis i) (h.heatCurve x t))
      (inner ℝ (h.eigenbasis i) v) (Ici 0) 0 := by
    simpa only [Function.comp_def, innerSL_apply_apply] using
      (innerSL ℝ (h.eigenbasis i)).hasFDerivAt.comp_hasDerivWithinAt 0 hv
  have hd : HasDerivWithinAt
      (fun t : ℝ => Real.exp (-t / i.1) * inner ℝ (h.eigenbasis i) x)
      (-i.1⁻¹ * inner ℝ (h.eigenbasis i) x) (Ici 0) 0 := by
    simpa only [neg_zero, zero_div, Real.exp_zero, mul_one] using
      ((compactHeatScalar_hasDerivAt i.1 0).mul_const (inner ℝ (h.eigenbasis i) x)).hasDerivWithinAt
  have hd' := hd.congr_of_mem (fun t ht => h.heatCurve_inner x ht i)
    (show (0 : ℝ) ∈ Ici 0 by simp)
  exact (hc.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (hd'.derivWithin (uniqueDiffWithinAt_Ici 0))

theorem CompactPositiveInverse.mem_inverse_domain_of_heatCurve_right_derivative {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) {x v : E}
    (hv : HasDerivWithinAt (h.heatCurve x) v (Ici 0) 0) :
    x ∈ (inverseOperator T h.injective).domain := by
  apply (h.mem_inverse_domain_iff x).mpr
  have he : (fun i : CompactSpectralIndex T => (i.1⁻¹ * inner ℝ (h.eigenbasis i) x) ^ 2) =
      (fun i : CompactSpectralIndex T => (inner ℝ (h.eigenbasis i) v) ^ 2) := by
    funext i
    rw [h.heatCurve_right_derivative_coeff hv i]
    ring
  rw [he]
  exact (h.hasSum_parseval v).summable

theorem CompactPositiveInverse.heatCurve_generator_iff {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x v : E) :
    HasDerivWithinAt (h.heatCurve x) v (Ici 0) 0 ↔
      ∃ hx : x ∈ (inverseOperator T h.injective).domain,
        v = -inverseOperator T h.injective ⟨x, hx⟩ := by
  constructor
  · intro hv
    refine ⟨h.mem_inverse_domain_of_heatCurve_right_derivative hv, ?_⟩
    apply h.eigenbasis.repr.injective
    apply lp.ext
    funext i
    simp only [HilbertBasis.repr_apply_apply]
    rw [h.heatCurve_right_derivative_coeff hv i, inner_neg_right, h.inner_eigenbasis_inverse]
    ring
  · rintro ⟨hx, rfl⟩
    exact h.heatCurve_right_derivative_zero ⟨x, hx⟩

theorem CompactPositiveInverse.heatCurve_right_differentiable_iff {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    DifferentiableWithinAt ℝ (h.heatCurve x) (Ici 0) 0 ↔
      x ∈ (inverseOperator T h.injective).domain := by
  constructor
  · intro hx
    exact h.mem_inverse_domain_of_heatCurve_right_derivative hx.hasDerivWithinAt
  · intro hx
    exact (h.heatCurve_right_derivative_zero ⟨x, hx⟩).differentiableWithinAt

end TimeTraps.Analysis
