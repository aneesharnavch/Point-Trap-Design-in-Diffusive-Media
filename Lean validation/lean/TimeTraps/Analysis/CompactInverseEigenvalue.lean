module

public import TimeTraps.Analysis.CompactInverseDomain

@[expose] public section

/-! Every actual inverse eigenvalue occurs in the constructed complete
spectral index. The argument uses a nonzero Hilbert-basis coefficient. -/

namespace TimeTraps.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem CompactPositiveInverse.exists_nonzero_coefficient {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) {x : E} (hx : x ≠ 0) :
    ∃ i : CompactSpectralIndex T, inner ℝ (h.eigenbasis i) x ≠ 0 := by
  by_contra he
  push Not at he
  apply hx
  apply h.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, he, inner_zero_right]

theorem CompactPositiveInverse.inverse_eigenvalue_index {T : E →L[ℝ] E}
    (h : CompactPositiveInverse T) {x : E} (hx : x ≠ 0) {ev : ℝ}
    (he : (x, ev • x) ∈ (inverseOperator T h.injective).graph) :
    ∃ i : CompactSpectralIndex T, i.1⁻¹ = ev := by
  obtain ⟨i, hi⟩ := h.exists_nonzero_coefficient hx
  have ht := (inverseOperator_graph_iff T h.injective x (ev • x)).mp he
  have hc := congrArg (fun v : E => inner ℝ (h.eigenbasis i) v) ht
  rw [h.inner_eigenbasis_apply, real_inner_smul_right] at hc
  have hs : i.1 * ev = 1 := by
    apply mul_right_cancel₀ hi
    simpa only [mul_assoc, one_mul] using hc
  refine ⟨i, ?_⟩
  symm
  rw [← one_div]
  apply (eq_div_iff (h.eigenbasis_positive i).ne').mpr
  simpa only [mul_comm] using hs

end TimeTraps.Analysis
