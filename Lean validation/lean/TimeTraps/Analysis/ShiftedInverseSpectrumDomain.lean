module

public import TimeTraps.Analysis.ShiftedInverseSpectrum
public import TimeTraps.Analysis.CompactInverseEigenvalue

@[expose] public section

/-! The domain of the actual translated inverse is exactly the space of
vectors whose translated eigenvalue coefficients are square summable.
The proof uses ordinary Parseval coefficients as well as the independently
proved reciprocal-domain criterion, including zero translated eigenvalues. -/

namespace TimeTraps.Analysis

open Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {T : E →L[ℝ] E}

theorem CompactPositiveInverse.mem_translated_domain_iff
    (h : CompactPositiveInverse T) (c : ℝ) (x : E) :
    x ∈ (translatedInverseOperator T h.injective c).domain ↔
      Summable (fun i : CompactSpectralIndex T =>
        ((i.1⁻¹ - c) * inner ℝ (h.eigenbasis i) x) ^ 2) := by
  constructor
  · intro hx
    exact (h.hasSum_translated_norm c ⟨x, hx⟩).summable
  · intro hx
    change x ∈ (inverseOperator T h.injective).domain
    apply (h.mem_inverse_domain_iff x).mpr
    have hc := (h.hasSum_parseval x).summable
    have hs := (hx.mul_left 2).add (hc.mul_left (2 * c ^ 2))
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hs
    intro i
    nlinarith [sq_nonneg ((i.1⁻¹ - c) * inner ℝ (h.eigenbasis i) x -
      c * inner ℝ (h.eigenbasis i) x)]

/-- Every actual eigenvalue, including zero, occurs in the translated
complete spectral index. -/
theorem CompactPositiveInverse.translated_eigenvalue_index
    (h : CompactPositiveInverse T) (c : ℝ) {x : E} (hx : x ≠ 0) {ev : ℝ}
    (he : (x, ev • x) ∈ (translatedInverseOperator T h.injective c).graph) :
    ∃ i : CompactSpectralIndex T, i.1⁻¹ - c = ev := by
  have hi : (x, (ev + c) • x) ∈ (inverseOperator T h.injective).graph := by
    rw [inverseOperator_graph_iff]
    have ht := (translatedInverseOperator_graph_iff T h.injective c x (ev • x)).mp he
    simpa only [add_smul] using ht
  obtain ⟨i, hi⟩ := h.inverse_eigenvalue_index hx hi
  exact ⟨i, by linarith⟩

end TimeTraps.Analysis
