module

public import TimeTraps.Spectral.CompactInverseResolvent
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-! Self-adjointness and positive quadratic form of the actual resolvent.
This is Hilbert-space positivity, with no order-preserving interpretation.
The strictly positive coefficients also give injectivity and strict
quadratic positivity at every nonzero vector. -/

namespace TimeTraps.Analysis

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.resolvent_symmetric {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) : (h.resolvent s).IsSymmetric := by
  intro x y
  have hx := h.eigenbasis.hasSum_inner_mul_inner (h.resolvent s x) y
  have hy := h.eigenbasis.hasSum_inner_mul_inner x (h.resolvent s y)
  have he : (fun i : CompactSpectralIndex T =>
      inner ℝ (h.resolvent s x) (h.eigenbasis i) * inner ℝ (h.eigenbasis i) y) =
      (fun i : CompactSpectralIndex T =>
      inner ℝ x (h.eigenbasis i) * inner ℝ (h.eigenbasis i) (h.resolvent s y)) := by
    funext i
    rw [real_inner_comm (h.eigenbasis i) (h.resolvent s x), h.resolvent_inner,
      h.resolvent_inner, real_inner_comm x]
    ring
  rw [he] at hx
  exact hx.unique hy

theorem CompactPositiveInverse.resolvent_selfAdjoint {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) : IsSelfAdjoint (h.resolvent s) :=
  (h.resolvent_symmetric s).isSelfAdjoint

theorem CompactPositiveInverse.hasSum_resolvent_quadratic {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x : E) :
    HasSum (fun i : CompactSpectralIndex T =>
      compactResolventCoefficient s i * (inner ℝ (h.eigenbasis i) x) ^ 2)
      (inner ℝ x (h.resolvent s x)) := by
  have hf : (fun i : CompactSpectralIndex T =>
      compactResolventCoefficient s i * (inner ℝ (h.eigenbasis i) x) ^ 2) =
      (fun i : CompactSpectralIndex T =>
        inner ℝ x (h.eigenbasis i) * inner ℝ (h.eigenbasis i) (h.resolvent s x)) := by
    funext i
    rw [h.resolvent_inner, real_inner_comm x]
    ring
  rw [hf]
  exact h.eigenbasis.hasSum_inner_mul_inner x (h.resolvent s x)

theorem CompactPositiveInverse.resolvent_nonneg {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) (x : E) :
    0 ≤ inner ℝ x (h.resolvent s x) := by
  rw [← (h.hasSum_resolvent_quadratic s x).tsum_eq]
  exact tsum_nonneg fun i => mul_nonneg (h.resolventCoefficient_pos s i).le (sq_nonneg _)

theorem CompactPositiveInverse.resolvent_injective {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) : Function.Injective (h.resolvent s) := by
  intro x y hxy
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply]
  have hi := congrArg (fun z => inner ℝ (h.eigenbasis i) z) hxy
  rw [h.resolvent_inner, h.resolvent_inner] at hi
  exact mul_left_cancel₀ (h.resolventCoefficient_pos s i).ne' hi

theorem CompactPositiveInverse.resolvent_positive {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (s : ℝ≥0) {x : E} (hx : x ≠ 0) :
    0 < inner ℝ x (h.resolvent s x) := by
  have hi : ∃ i : CompactSpectralIndex T, inner ℝ (h.eigenbasis i) x ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hx
    apply h.eigenbasis.repr.injective
    apply lp.ext
    funext i
    simp only [HilbertBasis.repr_apply_apply, hn i, inner_zero_right]
  obtain ⟨i, hi⟩ := hi
  rw [← (h.hasSum_resolvent_quadratic s x).tsum_eq]
  exact (h.hasSum_resolvent_quadratic s x).summable.tsum_pos
    (fun j => mul_nonneg (h.resolventCoefficient_pos s j).le (sq_nonneg _)) i
    (mul_pos (h.resolventCoefficient_pos s i) (sq_pos_of_ne_zero hi))

end TimeTraps.Analysis
