module

public import TimeTraps.Analysis.CompactSpectralDecay

@[expose] public section

/-! Hilbert-space and operator expansions for the eigenbasis constructed from
compactness, symmetry, positivity and injectivity.  All series are genuine
unconditional Hilbert-space or real series, without a chosen enumeration. -/

namespace TimeTraps.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.hasSum_eigenbasis {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    HasSum (fun i : CompactSpectralIndex T =>
      inner ℝ (h.eigenbasis i) x • h.eigenbasis i) x := by
  simpa only [HilbertBasis.repr_apply_apply] using h.eigenbasis.hasSum_repr x

theorem CompactPositiveInverse.hasSum_parseval {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    HasSum (fun i : CompactSpectralIndex T => (inner ℝ (h.eigenbasis i) x) ^ 2)
      (‖x‖ ^ 2) := by
  simpa only [real_inner_comm x, ← pow_two, real_inner_self_eq_norm_sq] using
    h.eigenbasis.hasSum_inner_mul_inner x x

theorem CompactPositiveInverse.parseval {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    ∑' i : CompactSpectralIndex T, (inner ℝ (h.eigenbasis i) x) ^ 2 = ‖x‖ ^ 2 :=
  (h.hasSum_parseval x).tsum_eq

theorem CompactPositiveInverse.inner_eigenbasis_apply {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) (i : CompactSpectralIndex T) :
    inner ℝ (h.eigenbasis i) (T x) = i.1 * inner ℝ (h.eigenbasis i) x := by
  calc
    inner ℝ (h.eigenbasis i) (T x) = inner ℝ (T (h.eigenbasis i)) x :=
      (h.symmetric.apply_clm _ _).symm
    _ = i.1 * inner ℝ (h.eigenbasis i) x := by
      rw [h.eigenbasis_eigen, real_inner_smul_left]

theorem CompactPositiveInverse.hasSum_apply {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    HasSum (fun i : CompactSpectralIndex T =>
      (i.1 * inner ℝ (h.eigenbasis i) x) • h.eigenbasis i) (T x) := by
  simpa only [h.inner_eigenbasis_apply] using h.hasSum_eigenbasis (T x)

theorem CompactPositiveInverse.hasSum_quadratic {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) (x : E) :
    HasSum (fun i : CompactSpectralIndex T =>
      i.1 * (inner ℝ (h.eigenbasis i) x) ^ 2) (inner ℝ x (T x)) := by
  have hf : (fun i : CompactSpectralIndex T => i.1 * (inner ℝ (h.eigenbasis i) x) ^ 2) =
      (fun i : CompactSpectralIndex T =>
        inner ℝ x (h.eigenbasis i) * inner ℝ (h.eigenbasis i) (T x)) := by
    funext i
    rw [h.inner_eigenbasis_apply, real_inner_comm x]
    ring
  rw [hf]
  exact h.eigenbasis.hasSum_inner_mul_inner x (T x)

end TimeTraps.Analysis
