module

public import TimeTraps.Analysis.InverseOperatorAdjoint
public import TimeTraps.Analysis.CompactSpectralReciprocal

@[expose] public section

/-! The reciprocal spectral vectors are eigenvectors of the actual
self-adjoint inverse operator. Its domain elements have the expected
reciprocal coefficients and unconditional inverse expansion. -/

namespace TimeTraps.Analysis

open Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.eigenbasis_mem_inverse_domain {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) :
    h.eigenbasis i ∈ (inverseOperator T h.injective).domain := by
  refine ⟨i.1⁻¹ • h.eigenbasis i, ?_⟩
  change T (i.1⁻¹ • h.eigenbasis i) = h.eigenbasis i
  rw [map_smul]
  exact h.reciprocal_eigen i

theorem CompactPositiveInverse.inverse_eigenbasis {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (i : CompactSpectralIndex T) :
    inverseOperator T h.injective ⟨h.eigenbasis i, h.eigenbasis_mem_inverse_domain i⟩ =
      i.1⁻¹ • h.eigenbasis i := by
  apply h.injective
  rw [inverseOperator_right_inverse, map_smul, h.reciprocal_eigen]

theorem CompactPositiveInverse.inner_eigenbasis_inverse {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain)
    (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i) (inverseOperator T h.injective x) =
      i.1⁻¹ * inner ℝ (h.eigenbasis i) (x : E) := by
  calc
    _ = i.1⁻¹ * inner ℝ (h.eigenbasis i) (T (inverseOperator T h.injective x)) := by
      rw [h.inner_eigenbasis_apply, ← mul_assoc, inv_mul_cancel₀ (h.eigenbasis_positive i).ne', one_mul]
    _ = _ := by rw [inverseOperator_right_inverse]

theorem CompactPositiveInverse.hasSum_inverse {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : (inverseOperator T h.injective).domain) :
    HasSum (fun i : CompactSpectralIndex T =>
      (i.1⁻¹ * inner ℝ (h.eigenbasis i) (x : E)) • h.eigenbasis i)
        (inverseOperator T h.injective x) := by
  simpa only [h.inner_eigenbasis_inverse] using h.hasSum_eigenbasis (inverseOperator T h.injective x)

end TimeTraps.Analysis
