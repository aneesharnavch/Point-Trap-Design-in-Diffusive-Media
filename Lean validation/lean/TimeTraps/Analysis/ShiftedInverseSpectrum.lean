module

public import TimeTraps.Analysis.ShiftedInverseOperator
public import TimeTraps.Analysis.CompactInverseDomainCharacterization

@[expose] public section

/-! The actual translated inverse has the original complete Hilbert
eigenbasis, with reciprocal eigenvalues translated by an arbitrary real
constant. Zero and negative translated eigenvalues are allowed. -/

namespace TimeTraps.Analysis

open Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {T : E →L[ℝ] E}

theorem CompactPositiveInverse.eigenbasis_mem_translated_domain
    (h : CompactPositiveInverse T) (c : ℝ) (i : CompactSpectralIndex T) :
    h.eigenbasis i ∈ (translatedInverseOperator T h.injective c).domain :=
  h.eigenbasis_mem_inverse_domain i

theorem CompactPositiveInverse.translated_eigenbasis
    (h : CompactPositiveInverse T) (c : ℝ) (i : CompactSpectralIndex T) :
    translatedInverseOperator T h.injective c ⟨h.eigenbasis i, h.eigenbasis_mem_translated_domain c i⟩ =
      (i.1⁻¹ - c) • h.eigenbasis i := by
  change inverseOperator T h.injective ⟨h.eigenbasis i, h.eigenbasis_mem_inverse_domain i⟩ -
    c • h.eigenbasis i = _
  rw [h.inverse_eigenbasis, sub_smul]

theorem CompactPositiveInverse.translated_eigenbasis_graph
    (h : CompactPositiveInverse T) (c : ℝ) (i : CompactSpectralIndex T) :
    (h.eigenbasis i, (i.1⁻¹ - c) • h.eigenbasis i) ∈
      (translatedInverseOperator T h.injective c).graph := by
  rw [translatedInverseOperator_graph_iff, ← add_smul, sub_add_cancel, map_smul]
  exact h.reciprocal_eigen i

theorem CompactPositiveInverse.inner_eigenbasis_translated
    (h : CompactPositiveInverse T) (c : ℝ)
    (x : (translatedInverseOperator T h.injective c).domain) (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i) (translatedInverseOperator T h.injective c x) =
      (i.1⁻¹ - c) * inner ℝ (h.eigenbasis i) (x : E) := by
  let y : (inverseOperator T h.injective).domain := ⟨(x : E), x.property⟩
  change inner ℝ (h.eigenbasis i) (inverseOperator T h.injective y - c • (y : E)) =
    (i.1⁻¹ - c) * inner ℝ (h.eigenbasis i) (y : E)
  rw [inner_sub_right, inner_smul_right, h.inner_eigenbasis_inverse]
  ring

theorem CompactPositiveInverse.hasSum_translated
    (h : CompactPositiveInverse T) (c : ℝ)
    (x : (translatedInverseOperator T h.injective c).domain) :
    HasSum (fun i : CompactSpectralIndex T =>
      ((i.1⁻¹ - c) * inner ℝ (h.eigenbasis i) (x : E)) • h.eigenbasis i)
        (translatedInverseOperator T h.injective c x) := by
  simpa only [h.inner_eigenbasis_translated] using
    h.hasSum_eigenbasis (translatedInverseOperator T h.injective c x)

theorem CompactPositiveInverse.hasSum_translated_norm
    (h : CompactPositiveInverse T) (c : ℝ)
    (x : (translatedInverseOperator T h.injective c).domain) :
    HasSum (fun i : CompactSpectralIndex T =>
      ((i.1⁻¹ - c) * inner ℝ (h.eigenbasis i) (x : E)) ^ 2)
        (‖translatedInverseOperator T h.injective c x‖ ^ 2) := by
  simpa only [h.inner_eigenbasis_translated] using
    h.hasSum_parseval (translatedInverseOperator T h.injective c x)

theorem CompactPositiveInverse.hasSum_translated_quadratic
    (h : CompactPositiveInverse T) (c : ℝ)
    (x : (translatedInverseOperator T h.injective c).domain) :
    HasSum (fun i : CompactSpectralIndex T =>
      (i.1⁻¹ - c) * (inner ℝ (h.eigenbasis i) (x : E)) ^ 2)
        (inner ℝ (x : E) (translatedInverseOperator T h.injective c x)) := by
  have hf : (fun i : CompactSpectralIndex T =>
      (i.1⁻¹ - c) * (inner ℝ (h.eigenbasis i) (x : E)) ^ 2) =
      (fun i : CompactSpectralIndex T => inner ℝ (x : E) (h.eigenbasis i) *
        inner ℝ (h.eigenbasis i) (translatedInverseOperator T h.injective c x)) := by
    funext i
    rw [h.inner_eigenbasis_translated, real_inner_comm (x : E)]
    ring
  rw [hf]
  exact h.eigenbasis.hasSum_inner_mul_inner (x : E) (translatedInverseOperator T h.injective c x)

end TimeTraps.Analysis
